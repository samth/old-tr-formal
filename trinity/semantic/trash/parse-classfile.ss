(module parse-classfile mzscheme
  (require (lib "contract.ss"))
  (require "../util/classfile.ss")
  (require "semantic-object.ss")

  (define (optional contract)
    (union contract false?))

  ;; parse-method-descriptor : input-port -> (cons (listof type-spec) type-spec)
  (define (parse-method-descriptor in)
    (let ([c (read-char in)])
      (if (char=? c #\()
          (let loop ([rev-formals null])
            (if (char=? (peek-char in) #\))
                (begin (read-char in)
                       (cons (reverse rev-formals) (parse-return-type in)))
                (loop (cons (parse-field-type in) rev-formals))))
          (error 'parse-method-descriptor "bad method descriptor: ~v" c))))

  ;; parse-return-type : input-port -> (optional type-spec)
  (define (parse-return-type in)
    (if (char=? (peek-char in) #\V)
        (begin (read-char in) #f)
        (parse-field-type in)))

  ;; parse-field-descriptor : input-port -> (promiseof type)
  (define (parse-field-descriptor in)
    (parse-field-type in))

  ;; parse-field-type : input-port -> (promiseof type)
  (define (parse-field-type in)
    (let ([c (read-char in)])
      (case c
        [(#\B) (delay byte)]
        [(#\C) (delay char)]
        [(#\D) (delay double)]
        [(#\F) (delay float)]
        [(#\I) (delay int)]
        [(#\J) (delay long)]
        [(#\S) (delay short)]
        [(#\Z) (delay boolean)]
        [(#\[) (let ([sub (parse-field-descriptor in)])
                 (delay (increase-type-dimension (force sub))))]
        [(#\L) (delay (get-type (parse-internal-type-name in)))]
        [else (error 'parse-field-type "bad field descriptor: ~v" c)])))

  ;; parse-internal-type-name : input-port -> (listof symbol)
  (define (parse-internal-type-name in)
    (define (parse-rev-elt rev-elt)
      (string->symbol (list->string (reverse rev-elt))))
    (let loop ([rev-elt null]
               [rev-path null])
      (let ([c (read-char in)])
        (case c
          [(#\;) (reverse (cons (parse-rev-elt rev-elt)
                                rev-path))]
          [(#\/) (loop null (cons (parse-rev-elt rev-elt)
                                  rev-path))]
          [else (loop (cons c rev-elt) rev-path)]))))

  )
