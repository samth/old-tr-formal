(module classfile mzscheme
  (require (lib "contract.ss"))
  (require (lib "match.ss"))
  (require (lib "list.ss" "srfi" "1"))
  (require (lib "etc.ss"))
  (require "binary-io.ss")
  (require "../lang/struct.ss")
  (require "../lang/hierarchy.ss")

  ;; obseleted by 299
  #;(define (byte? v)
    (and (integer? v)
         (<= 0 v 255)))

  (with-public-inspector
   (define-struct-hierarchy
    (info ()
      (class-info ((name-index natural-number/c)))
      (ref-info ((class-index natural-number/c)
                 (name-and-type-index natural-number/c))
        (field-ref-info ())
        (method-ref-info ())
        (interface-method-ref-info ()))
      (string-info ((string-index natural-number/c)))
      (integer-info ((bytes (listof byte?))))
      (float-info ((bytes (listof byte?))))
      (long-info ((high-bytes (listof byte?))
                  (low-bytes (listof byte?))))
      (double-info ((high-bytes (listof byte?))
                    (low-bytes (listof byte?))))
      (name-and-type-info ((name-index natural-number/c)
                           (descriptor-index natural-number/c)))
      (utf8-info ((length natural-number/c)
                  (bytes (listof byte?))))
      (inner-class-entry ((inner-class-info-index natural-number/c)
                          (outer-class-info-index natural-number/c)
                          (inner-name-index natural-number/c)
                          (inner-class-access-flags integer?))) ; TODO: is that right?
      (element-info ((access-flags integer?) ; TODO: is that right?
                     (name-index natural-number/c)
                     (descriptor-index natural-number/c)
                     (attributes-count natural-number/c)
                     (attributes (listof attribute-info?))) ; TODO: length == count
        (field-info ())
        (method-info ()))
      (attribute-info ()
        (unsupported-attribute-info ((length natural-number/c)
                                     (bytes (listof byte?))))
        (constant-value-attribute-info ((value-index natural-number/c)))
        (code-attribute-info ()) ; TODO: implement this
        (exceptions-attribute-info ((count natural-number/c)
                                    (exceptions (listof natural-number/c))))
        (inner-classes-attribute-info ())
        (synthetic-attribute-info ())
        (source-file-attribute-info ())
        (line-number-table-attribute-info ())
        (local-variable-table-attribute-info ())
        (deprecated-attribute-info ()))))


;   (define-struct class-info (name-index))
;   (define-struct field-ref-info (class-index name-and-type-index))
;   (define-struct method-ref-info (class-index name-and-type-index))
;   (define-struct interface-method-ref-info (class-index name-and-type-index))
;   (define-struct string-info (string-index))
;   (define-struct integer-info (bytes))
;   (define-struct float-info (bytes))
;   (define-struct long-info (high-bytes low-bytes))
;   (define-struct double-info (high-bytes low-bytes))
;   (define-struct name-and-type-info (name-index descriptor-index))
;   (define-struct utf8-info (length bytes))
;
;   (define-struct inner-class-entry (inner-class-info-index outer-class-info-index inner-name-index inner-class-access-flags))
;
;   (define-struct element-info (access-flags name-index descriptor-index attributes-count attributes))
;   (define-struct (field-info element-info) ())
;   (define-struct (method-info element-info) ())
;   (define-struct attribute-info ())
;   (define-struct (unsupported-attribute-info attribute-info) (length bytes))
;   (define-struct (constant-value-attribute-info attribute-info) (value-index))
;   (define-struct (code-attribute-info attribute-info) ())
;   (define-struct (exceptions-attribute-info attribute-info) (count exceptions))
;   (define-struct (inner-classes-attribute-info attribute-info) ())
;   (define-struct (synthetic-attribute-info attribute-info) ())
;   (define-struct (source-file-attribute-info attribute-info) ())
;   (define-struct (line-number-table-attribute-info attribute-info) ())
;   (define-struct (local-variable-table-attribute-info attribute-info) ())
;   (define-struct (deprecated-attribute-info attribute-info) ())

   (define-struct class-file (pool flags this super interfaces fields methods attributes))

   (provide (struct class-file (pool flags this super interfaces fields methods attributes)))
   )

  (define (read-constant in)
    (let ([type (char->integer (read-char in))])
      (case type
        [(1)  (read-utf8-info in)]
        [(3)  (read-integer-info in)]
        [(4)  (read-float-info in)]
        [(5)  (read-long-info in)]
        [(6)  (read-double-info in)]
        [(7)  (read-class-info in)]
        [(8)  (read-string-info in)]
        [(9)  (read-field-ref-info in)]
        [(10) (read-method-ref-info in)]
        [(11) (read-interface-method-ref-info in)]
        [(12) (read-name-and-type-info in)]
        [else (raise-io-error in "bad constant type: ~v" type)])))

  (define (read-class-info in)
    (make-class-info (read-format 2 'int in)))

  (define (read-field-ref-info in)
    (let ([class-index         (read-format 2 'int in)]
          [name-and-type-index (read-format 2 'int in)])
      (make-field-ref-info class-index name-and-type-index)))

  (define (read-method-ref-info in)
    (let ([class-index         (read-format 2 'int in)]
          [name-and-type-index (read-format 2 'int in)])
      (make-method-ref-info class-index name-and-type-index)))

  (define (read-interface-method-ref-info in)
    (let ([class-index         (read-format 2 'int in)]
          [name-and-type-index (read-format 2 'int in)])
      (make-interface-method-ref-info class-index name-and-type-index)))

  (define (read-string-info in)
    (make-string-info (read-format 2 'int in)))

  (define (read-integer-info in)
    (make-integer-info (read-format 4 'int in)))

  (define (read-float-info in)
    (make-float-info (read-format 4 'bytes in)))

  (define (read-long-info in)
    (let ([high-bytes (read-format 4 'bytes in)]
          [low-bytes  (read-format 4 'bytes in)])
      (make-long-info high-bytes low-bytes)))

  (define (read-double-info in)
    (let ([high-bytes (read-format 4 'bytes in)]
          [low-bytes  (read-format 4 'bytes in)])
      (make-double-info high-bytes low-bytes)))

  (define (read-name-and-type-info in)
    (let ([name-index       (read-format 2 'int in)]
          [descriptor-index (read-format 2 'int in)])
      (make-name-and-type-info name-index descriptor-index)))

  (define (read-utf8-info in)
    (let* ([len   (read-format 2 'int in)]
           [bytes (read-format len 'bytes in)])
      (make-utf8-info len bytes)))

  (define (constant-entry-count constant)
    (if (or (long-info? constant) (double-info? constant)) 2 1))

  (define (read-constant-pool count in)
    (let ([pool (make-vector count #f)])
      (let loop ([i 0])
        (when (< i count)
          (let ([next-constant (read-constant in)])
            (vector-set! pool i next-constant)
            (loop (+ i (constant-entry-count next-constant))))))
      pool))

  (define (read-field-info pool)
    (lambda (in)
      (let* ([access-flags     (read-format 2 'int in)]
             [name-index       (read-format 2 'int in)]
             [descriptor-index (read-format 2 'int in)]
             [attributes-count (read-format 2 'int in)]
             [attributes       (build-list attributes-count
                                           (lambda (i) ((read-attribute-info pool) in)))])
        (make-field-info access-flags name-index descriptor-index attributes-count attributes))))

  (define (read-method-info pool)
    (lambda (in)
      (let* ([access-flags     (read-format 2 'int in)]
             [name-index       (read-format 2 'int in)]
             [descriptor-index (read-format 2 'int in)]
             [attributes-count (read-format 2 'int in)]
             [attributes       (build-list attributes-count
                                           (lambda (i) ((read-attribute-info pool) in)))])
        (make-method-info access-flags name-index descriptor-index attributes-count attributes))))

  ;; TODO: optional extra argument to handle new attribute types
  (define (read-attribute-info pool)
    (lambda (in)
      (let* ([name-index (read-format 2 'int in)]
             [name (parse-utf8-info (vector-ref pool (sub1 name-index)))])
        (match name
          ["ConstantValue" (read-constant-value-attribute-info in)]
;          ["Code" (read-code-attribute-info in)]
          ["Exceptions" (read-exceptions-attribute-info in)]
;          ["InnerClasses" (read-inner-classes-attribute-info in)]
;          ["Synthetic" (read-inner-classes-attribute-info in)]
;          ["SourceFile" (read-source-file-attribute-info in)]
;          ["LineNumberTable" (read-line-number-table-attribute-info in)]
;          ["LocalVariableTable" (read-local-variable-table-attribute-info in)]
          ["Deprecated" (read-deprecated-attribute-info in)]
          [_ (read-unsupported-attribute-info in)]))))

  (define (read-inner-classes-attribute-info in)
    (let* ([attribute-length (read-format 4 'int in)]
           [count            (read-format 2 'int in)]
           [classes          (build-list count (lambda (i) (read-inner-class-entry in)))])
      (make-inner-classes-attribute-info count classes)))

  (define (read-inner-class-entry in)
    (let* ([inner-class-info-index   (read-format 2 'int)]
           [outer-class-info-index   (read-format 2 'int)]
           [inner-name-index         (read-format 2 'int)]
           [inner-class-access-flags (read-format 2 'int)])
      (make-inner-class-entry inner-class-info-index outer-class-info-index inner-name-index inner-class-access-flags)))

  (define (read-exceptions-attribute-info in)
    (let* ([attribute-length (read-format 4 'int in)]
           [count            (read-format 2 'int in)]
           [exceptions       (build-list count (lambda (i) (read-format 2 'int in)))])
      ;(fprintf (current-error-port) "Exceptions: ~v~n" exceptions)
      (make-exceptions-attribute-info count exceptions)))

  (define (read-constant-value-attribute-info in)
    (let ([attribute-length (read-format 4 'int in)])
      (unless (= attribute-length 2)
        (raise-io-error 'read-attribute-info
                        "attribute ConstantValue: expected 2 bytes, found ~a bytes" attribute-length))
      (make-constant-value-attribute-info (read-format 2 'int in))))

  (define (read-synthetic-attribute-info in)
    (let ([attribute-length (read-format 4 'int in)])
      (unless (zero? attribute-length)
        (raise-io-error 'read-attribute-info
                        "attribute Synthetic: expected 0 bytes, found ~a bytes" attribute-length))
      (make-synthetic-attribute-info)))

  (define (read-deprecated-attribute-info in)
    (let ([attribute-length (read-format 4 'int in)])
      (unless (zero? attribute-length)
        (raise-io-error 'read-attribute-info
                        "attribute Deprecated: expected 0 bytes, found ~a bytes" attribute-length))
      (make-deprecated-attribute-info)))

  (define (read-unsupported-attribute-info in)
    (let* ([attribute-length (read-format 4 'int in)]
           [info             (read-format attribute-length 'bytes in)])
      (make-unsupported-attribute-info attribute-length info)))

  (define (read-interfaces count in pool)
    (map (lambda (i) (vector-ref pool (sub1 i)))
         (build-list count (lambda (i) (read-format 2 'int in)))))

  ;; read-array : natural-number input-port (input-port -> a) -> (vectorof a)
  (define (read-array count in reader)
    (build-vector count (lambda (i) (reader in))))

  ;; read-list : natural-number input-port (input-port -> a) -> (listof a)
  (define (read-list count in reader)
    (build-list count (lambda (i) (reader in))))

  ;; read-class-file : input-port -> classfile
  (define (read-class-file in)
    (let ([magic (read-format 4 'int in #f)])
      (unless (= magic #xCAFEBABE)
        (raise-io-error in "bad magic number: ~x" magic))
      (let* ([minor               (read-format 2 'int in)]
             [major               (read-format 2 'int in)]
             [constant-pool-count (read-format 2 'int in)]
             [pool                (read-constant-pool (sub1 constant-pool-count) in)]
             [access-flags        (read-format 2 'int in)]
             [this-index          (read-format 2 'int in)]
             [super-index         (read-format 2 'int in)]
             [interfaces-count    (read-format 2 'int in)]
             [interfaces          (read-interfaces interfaces-count in pool)]
             [fields-count        (read-format 2 'int in)]
             [fields              (read-list fields-count in (read-field-info pool))]
             [methods-count       (read-format 2 'int in)]
             [methods             (read-list methods-count in (read-method-info pool))]
             [attributes-count    (read-format 2 'int in)]
             [attributes          (read-list attributes-count in (read-attribute-info pool))])
;                                  (begin
;                                    (fprintf (current-error-port) "attributes: ~a~n" attributes-count)
;                                    (printf "methods-count: ~a~n" methods-count)
;                                    (printf "access-flags: ~x~n" access-flags)
;                                    (fprintf (current-error-port) "pool: ~v~n"
;                                             (let ([pool* (vector->list pool)])
;                                               (map (lambda (entry)
;                                                      (if (utf8-info? entry)
;                                                          (parse-utf8-info entry)
;                                                          entry))
;                                                    pool*)))
        (make-class-file pool access-flags this-index super-index interfaces fields methods attributes))))

;        (let* ([deref (lambda (i) (vector-ref pool (sub1 i)))]
;               [parse-class-info (lambda (ci) (parse-utf8-info (deref (class-info-name-index ci))))])
;          (make-class-file #f;pool
;                           (parse-flags access-flags)
;                           (parse-class-info (deref this-index))
;                           (parse-class-info (deref super-index))
;                           (map parse-class-info interfaces)
;                           fields
;                           methods
;                           attributes)))))

  ;; Parsers:

  ;; TODO: real UTF8 parsing
  (define (parse-utf8-info utf8)
    (list->string (map integer->char (utf8-info-bytes utf8))))

  (define access-flags
    (list->vector '(public      ; #x0001
                    private     ; #x0002
                    protected   ; #x0004
                    static      ; #x0008
                    final       ; #x0010
                    super       ; #x0020
                    volatile    ; #x0040
                    transient   ; #x0080
                    native      ; #x0100
                    interface   ; #x0200
                    abstract    ; #x0400
                    strictfp))) ; #x0800

  (define (parse-flags bits)
    (filter-map identity
                (build-list (vector-length access-flags)
                            (lambda (i)
                              (and (bit-enabled? bits i)
                                   (vector-ref access-flags i))))))

  (provide read-class-file parse-utf8-info parse-flags))
