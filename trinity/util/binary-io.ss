(module binary-io mzscheme
  (require (lib "etc.ss"))

  ;; TODO: contracts

  ;; a byte is an integer in the range [0,255]
  ;; a parsed is one of:
  ;;   - integer
  ;;   - (listof byte)
  ;;   - (listof char)
  ;;   - string

  (define skip
    (opt-lambda (bytes [in (current-input-port)])
      (read-bytes bytes in)
      (void)))

  (define (bit-enabled? n i)
    (not (zero? (bitwise-and n (arithmetic-shift 1 i)))))

  ;; TODO: these are wrong. fix them.
  (define (make-big-endian chars)
    (make-small-endian (reverse chars)))

  (define (make-small-endian chars)
    (let loop ([chars chars] [n 0] [mult 1])
      (if (null? chars)
          n
          (loop (cdr chars)
                (+ n (* mult (car chars)))
                (* mult 256)))))

  (define (chars->ints cs)
    cs)
    ;(map char->integer cs))

  (define (make-parser type small-endian?)
    (case type
      [(int) (if small-endian? make-small-endian make-big-endian)]
      [(bytes) chars->ints]    ; TODO: endianness?
      [(chars) identity]       ; TODO: endianness?
      [(string) list->bytes]
      ;TODO: [(c-string) ?]
      [else (error 'read/layout "bad layout type: ~v" type)]))

  ;; TODO: implement with read-string instead?
  ;; read-chars : natural-number input-port -> (listof byte)
  (define read-chars
    (opt-lambda (n [in (current-input-port)])
      (build-list n (lambda (i) (read-byte in)))))

  (define peek-chars
    (opt-lambda (n [in (current-input-port)])
      (string->list (peek-bytes n 0 in))))

  (define peek-format
    (opt-lambda (count type [in (current-input-port)] [small-endian? #f])
      ((make-parser type small-endian?) (peek-chars count in))))

  (define read-format
    (opt-lambda (count type [in (current-input-port)] [small-endian? #f])
      ((make-parser type small-endian?) (read-chars count in))))

  (define (raise-io-error port msg . args)
    (error (apply format msg args)))

  (provide bit-enabled? ;make-small-endian make-big-endian
           read-chars peek-chars skip
           read-format peek-format
           raise-io-error))
