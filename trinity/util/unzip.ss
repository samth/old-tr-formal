(module unzip mzscheme
  (require (lib "contract.ss"))
  (require (lib "etc.ss"))
  (require (lib "inflate.ss"))
  (require (lib "thread.ss"))
  (require (lib "port.ss"))
  (require "../lang/struct.ss")
  (require "binary-io.ss")

  (define *local-file-header*                      #x04034b50)
  (define *archive-extra-record*                   #x08064b50)
  (define *central-file-header*                    #x02014b50)
  (define *digital-signature*                      #x05054b50)
  (define *zip64-end-of-central-directory-record*  #x06064b50)
  (define *zip64-end-of-central-directory-locator* #x07064b50)
  (define *end-of-central-directory-record*        #x06054b50)

  ;; unzip-one-file : input-port (string -> output-port) -> any
  ;; unzips a single file and positions the input stream at the next section
  (define (unzip-one-entry in build-out)
    (let ([rf (lambda (count type) (read-format count type in #t))])
      (let* ([signature            (rf 4 'int)]
             [version              (rf 2 'bytes)]
             [bits                 (rf 2 'int)]
             [compression          (rf 2 'int)]
             [time                 (rf 2 'int)]
             [date                 (rf 2 'int)]
             [crc-32               (rf 4 'int)]
             [compressed           (rf 4 'int)]
             [uncompressed         (rf 4 'int)]
             [filename-length      (rf 2 'int)]
             [extra-length         (rf 2 'int)]
             [filename             (rf filename-length 'string)]
             [extra                (rf extra-length 'bytes)])
        (let ([out (build-out filename)]
              [in0 (if (bit-enabled? bits 3)
                       in
                       (make-limited-input-port in compressed #f))])
          (if (zero? compression)
              (copy-port in0 out)
              (inflate in0 out))
          (when (bit-enabled? bits 3)
            ;; TODO: I don't understand this extra signature
            (when (string=? (peek-string 2 0 in) "PK")
              (skip 4 in))
            (skip 12 in))))))

  ;; unzip : input-port (string -> output-port) -> any
  (define (unzip in build-out)
    (when (= (peek-format 4 'int in #t) *local-file-header*)
      (unzip-one-entry in build-out)
      (unzip in build-out)))

  ;; find-central-directory : input-port -> natural-number natural-number natural-number
  (define (find-central-directory in size)
    (let loop ([pos (- size 18)])
      (unless (positive? pos)
        (raise-io-error 'find-central-directory "no end record"))
      (file-position in pos)
      (let* ([rf (lambda (count type) (read-format count type in #t))]
             [signature (rf 4 'int)])
        (if (= signature *end-of-central-directory-record*)
            (let ([disk-number       (rf 2 'int)]
                  [directory-disk    (rf 2 'int)]
                  [disk-entries      (rf 2 'int)]
                  [entry-count       (rf 2 'int)]
                  [directory-length  (rf 4 'int)]
                  [directory-offset  (rf 4 'int)]
                  [comment-length    (rf 2 'int)])
              (if (= (- size (file-position in)) comment-length)
                  (values directory-offset directory-length entry-count)
                  (loop (sub1 pos))))
            (loop (sub1 pos))))))

  ;; read-central-directory : input-port natural-number -> (listof (cons string natural-number))
  (define (read-central-directory in size)
    (let-values ([(offset length count)
                  (find-central-directory in size)])
      (file-position in offset)
      (build-list count
                  (lambda (i)
                    (let* ([rf (lambda (count type) (read-format count type in #t))]
                           [signature (rf 4 'int)])
                      (unless (= signature *central-file-header*)
                        (raise-io-error 'read-central-directory
                                        "bad central file header signature: ~x" signature))
                      (let ([version             (rf 2 'int)]
                            [required            (rf 2 'int)]
                            [bits                (rf 2 'int)]
                            [compression         (rf 2 'int)]
                            [time                (rf 2 'int)]
                            [date                (rf 2 'int)]
                            [crc-32              (rf 4 'int)]
                            [compressed          (rf 4 'int)]
                            [uncompressed        (rf 4 'int)]
                            [filename-length     (rf 2 'int)]
                            [extra-length        (rf 2 'int)]
                            [comment-length      (rf 2 'int)]
                            [disk-number         (rf 2 'int)]
                            [internal-attributes (rf 2 'int)]
                            [external-attributes (rf 4 'int)]
                            [relative-offset     (rf 4 'int)])
                        (let ([filename (rf filename-length 'string)])
                          (skip (+ extra-length comment-length) in)
                          (cons filename relative-offset))))))))

  ;; zip-file a = (listof string) (string -> a)
  (with-public-inspector
   (define-struct zip-file (entries inflate))
   (provide/contract (struct zip-file ((entries (listof string?))
                                       (inflate (string? . -> . any/c))))))

  ;; TODO: memory leak?

  (define (unzip/lazy path parse-entry)
    (printf "in unzip/lazy!!!~n")
    (let ([entries (make-hash-table 'equal)]
          [directory (with-input-from-file path
                       (lambda ()
                         (read-central-directory (current-input-port)
                                                 (file-size path))))])
      (for-each (lambda (pair)
                  (let ([filename (car pair)]
                        [offset (cdr pair)])
                    (hash-table-put!
                     entries
                     filename
                     (delay
                       (let-values ([(entry-in entry-out) (make-pipe)])
                         (thread
                          (lambda ()
                            (dynamic-wind void
                                          (lambda ()
                                            (with-input-from-file path
                                              (lambda ()
                                                (file-position (current-input-port)
                                                               offset)
                                                (unzip-one-entry (current-input-port)
                                                                 (lambda (name) entry-out)))))
                                          (lambda ()
                                            (close-output-port entry-out)))))
                         (parse-entry filename entry-in))))))
                directory)
      (make-zip-file
       (map car directory)
       (lambda (filename)
         (cond
           [(hash-table-get entries filename (lambda () #f)) => force]
           [else #f])))))

  ;; unzip/lazy : string (string input-port -> a) -> zip-file a
;  (define (unzip/lazy path parse-entry)
;    (let* ([in (open-input-file path)]
;           [entries (make-hash-table 'equal)]
;           [directory (read-central-directory in (file-size path))])
;      (let ([ref-count (length directory)])
;        (for-each (lambda (pair)
;                    (let ([filename (car pair)]
;                          [offset (cdr pair)])
;                      (hash-table-put!
;                       entries
;                       filename
;                       (delay
;                         (let-values ([(entry-in entry-out) (make-pipe)])
;                           (dynamic-wind
;                            void
;                            (lambda ()
;                              (let ([reader (thread
;                                             (lambda ()
;                                               (dynamic-wind
;                                                void
;                                                (lambda ()
;                                                  (file-position in offset)
;                                                  (unzip-one-entry in (lambda (name) entry-out)))
;                                                (lambda ()
;                                                  (close-output-port entry-out)))))])
;                                (parse-entry filename entry-in)))
;                            (lambda ()
;                              (set! ref-count (sub1 ref-count))
;                              (when (zero? ref-count)
;                                ;(fprintf (current-error-port) "closing zip file~n")
;                                (close-input-port in)))))))))
;                  directory)
;        (make-zip-file
;         (map car directory)
;         (lambda (filename)
;           (cond
;             [(hash-table-get entries filename (lambda () #f)) => force]
;             [else #f]))))))

  (provide unzip unzip/lazy))
