(module analyze-classfile mzscheme
  (require (lib "string.ss" "srfi" "13"))
  (require (lib "list.ss" "srfi" "1"))
  (require (all-except (lib "class.ss") class-info))
  (require (lib "match.ss"))
  (require (lib "string.ss"))
  (require (lib "etc.ss"))
  (require "semantic-object.ss")
  (require "class-resolver.ss")
  (require "../util/classfile.ss")
  (require "../lang/to-string.ss")

  ;; parse-type-path : string -> (listof symbol)
  (define (parse-type-path path)
    (map string->symbol (regexp-split "/" path)))

  (define type-modifiers
    '(public private protected static final abstract strictfp))

  (define (pretty-type t)
    (cond
      [(type-name? t) (type-name->string t)]
      [(is-a? t to-string<%>) (send t to-string)]
      [(not t) "void"]
      [else (format "~a" t)]))
  (define (pretty-formals fmls)
    (string-append
     "(" (string-join (map pretty-type fmls) ", ") ")"))

  ;; analyze-classfile : class-file -> declared-type%
  (define (analyze-classfile cf)
    (define deref
      (let ([pool (class-file-pool cf)])
        (lambda (i)
          (vector-ref pool (sub1 i)))))
    (define (find-class-name cinfo)
      (parse-utf8-info (deref (class-info-name-index cinfo))))
    (define (super)
      (let ([index (class-file-super cf)])
        (if (zero? index)
            null
            (parse-type-path
             (find-class-name (deref index))))))
    (define (this)
      (parse-type-path
       (find-class-name
        (deref (class-file-this cf)))))

    (define (analyze-field field)
      (match field
        [($ field-info flag-bits name-index descriptor-index attributes-count attributes)
         (let ([flags (parse-flags flag-bits)]
               [name (parse-utf8-info (deref name-index))]
               [type-name (parse-field-descriptor
                           (open-input-string
                            (parse-utf8-info (deref descriptor-index))))])
           (make-object field% name flags type-name))]))
    (define (analyze-method method)
      (match method
        [($ method-info flag-bits name-index descriptor-index attributes-count attributes)
         (let* ([flags (parse-flags flag-bits)]
                [name (parse-utf8-info (deref name-index))]
                [method-desc (parse-method-descriptor
                              (open-input-string
                               (parse-utf8-info (deref descriptor-index))))]
                [formals (method-descriptor-formals method-desc)]
                [exceptions (cond
                              [(find exceptions-attribute-info? attributes)
                               => (lambda (info)
                                    (map (compose build-type-name parse-type-path find-class-name deref)
                                         (exceptions-attribute-info-exceptions info)))]
                              [else null])]
                [return (method-descriptor-return method-desc)])
           (cond
             [(string=? name "<init>")
              (make-object constructor%
                (symbol->string (last (this)))
                formals
                exceptions)]
             [(string=? name "<clinit>")
              (make-object initializer%)]
             [else
              (make-object method%
                name
                formals
                exceptions
                (method-descriptor-return method-desc))]))]))

    (let* ([flags (parse-flags (class-file-flags cf))]
           [modifiers (lset-intersection eq? flags type-modifiers)])
      (printf "in analyze-classfile~n")
      (match cf
        [($ class-file _ _ _ _ iface-infos fields methods attributes)
         (match (build-type-name (this))
           [($ type-name package name)
            (let ([interfaces (map (compose build-type-name parse-type-path find-class-name)
                                   iface-infos)]
                  [members (append (map analyze-field fields)
                                   (map analyze-method methods))])
              (if (memq 'interface flags)
                  (make-object interface%
                    package name
                    modifiers interfaces members)
                  (make-object class%
                    package name
                    modifiers interfaces members
                    (super))))])])))

  ;; ===========================================================================
  ;; INTERNAL TYPE DESCRIPTOR PARSER
  ;; ===========================================================================

  ;; method-descriptor : (listof lazy-type) lazy-type
  (define-struct method-descriptor (formals return))

  ;; parse-method-descriptor : input-port -> (cons (listof lazy-type) lazy-type)
  (define (parse-method-descriptor in)
    (let ([c (read-char in)])
      (if (char=? c #\()
          (let loop ([rev-formals null])
            (if (char=? (peek-char in) #\))
                (begin (read-char in)
                       (make-method-descriptor (reverse rev-formals)
                                               (parse-return-type in)))
                (loop (cons (parse-field-type in) rev-formals))))
          (error 'parse-method-descriptor "bad method descriptor: ~v" c))))

  ;; lazy-type = (union type<%> type-name)
  ;(define lazy-type (union (is-a?/c type<%>) type-name?))

  ;; parse-return-type : input-port -> (optional lazy-type)
  (define (parse-return-type in)
    (if (char=? (peek-char in) #\V)
        (begin (read-char in) #f)
        (parse-field-type in)))

  ;; parse-field-descriptor : input-port -> lazy-type
  (define (parse-field-descriptor in)
    (parse-field-type in))

  ;; parse-field-type : input-port -> lazy-type
  (define (parse-field-type in)
    (let ([c (read-char in)])
      (case c
        [(#\B) byte]
        [(#\C) char]
        [(#\D) double]
        [(#\F) float]
        [(#\I) int]
        [(#\J) long]
        [(#\S) short]
        [(#\Z) boolean]
        [(#\[) (make-object array-type% (parse-field-descriptor in))]
        [(#\L) (parse-internal-type-name in)]
        [else  (error 'parse-field-type "bad field descriptor: ~v" c)])))

  ;; parse-internal-type-name : input-port -> type-name
  (define (parse-internal-type-name in)
    (define (parse-rev-elt rev-elt)
      (string->symbol (list->string (reverse rev-elt))))
    (define (return rev-elt rev-path)
      (build-type-name (reverse (cons (parse-rev-elt rev-elt) rev-path))))
    (let loop ([rev-elt null]
               [rev-path null])
      (let ([c (read-char in)])
        (if (eof-object? c)
            (return rev-elt rev-path)
            (case c
              [(#\;) (return rev-elt rev-path)]
              [(#\/) (loop null (cons (parse-rev-elt rev-elt) rev-path))]
              [else  (loop (cons c rev-elt) rev-path)])))))

  (provide analyze-classfile))
