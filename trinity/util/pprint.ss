#cs
(module pprint mzscheme
  (require (lib "contract.ss"))
  (require (lib "match.ss"))
  (require (all-except (lib "list.ss") empty))
  (require (lib "etc.ss"))
  (require "../lang/datatype.ss")

  ;; ===========================================================================
  ;; Primitives
  ;; ===========================================================================

  (define-datatype Doc
    [NIL     ()]
    [SEQ     (left right)]
    [NEST    (depth doc)]
    [LABEL   (label doc)]
    [TEXT    (text)]
    [LINE    (break?)]
    [GROUP   (doc)]
    [DOC     (max-depth value)]
    [COLUMN  (f)]
    [NESTING (f)])

  (define (beside x y)  (make-SEQ x y))
  (define empty         (make-NIL))
  (define (nest i x)    (make-NEST i x))
  (define (text s)      (make-TEXT s))
  (define (column f)    (make-COLUMN f))
  (define (nesting f)   (make-NESTING f))
  (define (group x)     (make-GROUP x))
  (define (char c)      (if (char=? c #\newline) line (text (string c))))

  (define line          (make-LINE #f))
  (define linebreak     (make-LINE #t))
  (define softline      (group line))
  (define softbreak     (group linebreak))

  ;; ===========================================================================
  ;; Semi-primitives
  ;; ===========================================================================

  (define (fill-break f x)
    (width x (lambda (w)
               (if (> w f)
                   (nest f linebreak)
                   (text (spaces (- f w)))))))
  (define (fill f d)
    (width d (lambda (w)
               (if (>= w f)
                   empty
                   (text (spaces (- f w)))))))
  (define (width d f)
    (column (lambda (k1)
              (<> d (column (lambda (k2)
                              (f (- k2 k1))))))))
  (define (indent i d)
    (hang i (<> (text (spaces i)) d)))
  (define (hang i d)
    (align (nest i d)))
  (define (align d)
    (column (lambda (k)
              (nesting (lambda (i)
                         (nest (- k i) d))))))

  ;; ===========================================================================
  ;; High-level combinators
  ;; ===========================================================================

  (define comma     (text ","))
  (define semi      (text ";"))
  (define colon     (text ":"))
  (define lparen    (text "("))
  (define rparen    (text ")"))
  (define lbracket  (text "["))
  (define rbracket  (text "]"))
  (define lbrace    (text "{"))
  (define rbrace    (text "}"))
  (define space     (text " "))
  (define ellipsis  (text "..."))
  (define squote    (text "'"))
  (define dquote    (text "\""))
  (define dot       (text "."))
  (define backslash (text "\\"))
  (define equals    (text "="))

  (define (foldr1 f xs)
    (match xs
      [(x) x]
      [(x . xs) (f x (foldr1 f xs))]))

  (define (fold f ds)
    (if (null? ds)
        empty
        (foldr1 f ds)))

  (define (cat-with sep)
    (letrec ([f (match-lambda
                  [()       empty]
                  [(x)      x]
                  [(x y)    (<> x sep y)]
                  [(d . ds) (<> d sep (f ds))])])
      (lambda ds
        (f ds))))

  (define <>
    (letrec ([f (match-lambda
                  [()       empty]
                  [(x)      x]
                  [(x y)    (beside x y)]
                  [(d . ds) (beside d (f ds))])])
      (lambda ds
        (f ds))))

  (define <+>           (cat-with space))
  (define </>           (cat-with softline))
  (define <//>          (cat-with softbreak))
  (define <$>           (cat-with line))
  (define <$$>          (cat-with linebreak))

  (define hsep          (lambda (ds) (fold <+> ds)))
  (define vsep          (lambda (ds) (fold <$> ds)))
  (define fill-sep      (lambda (ds) (fold </> ds)))
  (define sep           (compose group vsep))

  (define hcat          (lambda (ds) (fold <> ds)))
  (define vcat          (lambda (ds) (fold <$$> ds)))
  (define fill-cat      (lambda (ds) (fold <//> ds)))
  (define cat           (compose group vcat))

  (define (next-newline s i)
    (if (or (>= i (string-length s))
            (char=? (string-ref s i) #\newline))
        i
        (next-newline s (add1 i))))

  (define (split-newlines s)
    (let ([len (string-length s)])
      (let f ([start 0])
        (cond
          [(>= start len)
           null]
          [(char=? (string-ref s start) #\newline)
           (cons "\n" (f (add1 start)))]
          [else (let ([end (next-newline s start)])
                  (if (= end len)
                      (list (substring s start))
                      (cons (substring s start end)
                            (cons "\n" (f (add1 end))))))]))))

  (define (string->doc s)
    (foldr <>
           empty
           (map (lambda (s)
                  (if (string=? "\n" s)
                      line
                      (text s)))
                (split-newlines s))))

  (define (value->doc x)
    (string->doc (format "~a" x)))

  ;; (punctuate p (list d1 d2 ... dn)) => (list (<> d1 p) (<> d2 p) ... dn)

  (define (punctuate p ds)
    (match ds
      [() null]
      [(d) (list d)]
      [(d . ds) (cons (<> d p) (punctuate p ds))]))

  (define (spaces n)
    (list->string (build-list n (lambda (i) #\space))))
  (define (extend s n)
    (string-append s (spaces n)))

  ;; TODO: COLUMN and NESTING aren't quite right;
  ;;       they indent correctly but the breaking rules are wrong

  (define (layout concat w x s0)
    (letrec (;; best : integer string Doc ???
             [best (lambda (k0 is doc s0)
                     (match doc
                       [($ NIL)
                        (cons k0 s0)]
                       [($ SEQ x y)
                        (match-let ([(k1 . s1) (best k0 is x s0)])
                          (best k1 is y s1))]
                       [($ NEST n x)
                        (best k0 (extend is n) x s0)]
                       [($ LABEL l x)
                        (best k0 (string-append is l) x s0)]
                       [($ LINE _)
                        (cons (string-length is)
                              (concat is (concat "\n" s0)))]
                       [($ GROUP x)
                        (if (fits? x w k0 (string-length is))
                            (flat k0 is x s0)
                            (best k0 is x s0))]
                       [($ DOC md val)
                        ;; TODO: use max-depth
                        (best k0 is doc (value->doc val))]
                       [($ TEXT t)
                        (cons (+ k0 (string-length t))
                              (concat t s0))]
                       [($ COLUMN f)
                        (best k0 is (f k0) s0)]
                       [($ NESTING f)
                        (best k0 is (f (string-length is)) s0)]))]
             [flat (lambda (k0 is doc s0)
                     (match doc
                       [($ NIL)
                        (cons k0 s0)]
                       [($ SEQ x y)
                        (match-let ([(k1 . s1) (flat k0 is x s0)])
                          (flat k1 is y s1))]
                       [($ NEST _ x)
                        (flat k0 is x s0)]
                       [($ LABEL _ x)
                        (flat k0 is x s0)]
                       [($ LINE break?)
                        (if break?
                            (cons k0 s0)
                            (cons (add1 k0) (concat " " s0)))]
                       [($ GROUP x)
                        (flat k0 is x s0)]
                       [($ DOC md val)
                        ;; TODO: use max-depth
                        (flat k0 is (value->doc val) s0)]
                       [($ TEXT t)
                        (cons (+ k0 (string-length t))
                              (concat t s0))]
                       [($ COLUMN f)
                        (flat k0 is (f k0) s0)]
                       [($ NESTING f)
                        (flat k0 is (f (string-length is)) s0)]))])
      (best 0 "" x s0)))

  ;; fits? : Doc integer integer integer -> boolean
  ;; true if the flattened doc would fit on the remainder of the current line
  ;; w : line width
  ;; k : current column
  ;; i : current nesting level
  (define (fits? x w k i)
    (not (negative? (let/ec break
                      ;; space-left : Doc integer -> integer
                      ;; number of columns left after placing doc at column col
                      (let space-left ([doc x]
                                       [col (- w k)])
                        (when (negative? col)
                          (break col))
                        (match doc
                          [($ NIL) col]
                          [($ SEQ x y) (space-left y (space-left x col))]
                          [($ NEST _ x) (space-left x col)]
                          [($ LABEL _ x) (space-left x col)]
                          [($ LINE break?) (if break? col (sub1 col))]
                          [($ GROUP x) (space-left x col)]
                          [($ DOC md val) (space-left (value->doc val) col)]
                          [($ TEXT t) (- col (string-length t))]
                          [($ COLUMN f) (space-left (f col) col)]
                          [($ NESTING f) (space-left (f i) col)]))))))

  ;; ===========================================================================
  ;; Front-end and utilities
  ;; ===========================================================================

  (define current-page-width (make-parameter 80))

  (define-syntax with-output-to-string
    (syntax-rules ()
      [(_ e1 e2 ...)
       (let ([op (open-output-string)])
         (parameterize ((current-output-port op))
           e1 e2 ...
           (get-output-string op)))]))

  (define pretty-print
    (opt-lambda (doc [port (current-output-port)])
      (for-each (lambda (str)
                  (display str port))
                (reverse (cdr (layout cons (current-page-width) doc null))))))
  (provide/contract (pretty-print ((Doc?) (port?) . opt-> . any/c)))
  (provide current-page-width) ; current-ribbon-width

  (provide/contract (punctuate (Doc? (listof Doc?) . -> . (listof Doc?))))
  ; comma-brackets comma-parens space-parens semi-braces enclose-sep
  (provide/contract (empty Doc?)
                    (char (char? . -> . Doc?))
                    (text (string? . -> . Doc?))
                    (line Doc?)
                    (linebreak Doc?)
                    (softline Doc?)
                    (softbreak Doc?))
  (provide/contract (beside (Doc? Doc? . -> . Doc?))
                    (nest (natural-number/c Doc? . -> . Doc?))
                    (group (Doc? . -> . Doc?))
                    (column ((natural-number/c . -> . Doc?) . -> . Doc?))
                    (nesting ((natural-number/c . -> . Doc?) . -> . Doc?)))
  (provide/contract (align (Doc? . -> . Doc?))
                    (hang (natural-number/c Doc? . -> . Doc?))
                    (indent (natural-number/c Doc? . -> . Doc?))
                    (fill (natural-number/c Doc? . -> . Doc?))
                    (fill-break (natural-number/c Doc? . -> . Doc?))
                    (width (Doc? (natural-number/c . -> . Doc?) . -> . Doc?)))
  (provide/contract (<>   (() (listof Doc?) . ->* . (Doc?)))
                    (<+>  (() (listof Doc?) . ->* . (Doc?)))
                    (</>  (() (listof Doc?) . ->* . (Doc?)))
                    (<//> (() (listof Doc?) . ->* . (Doc?)))
                    (<$>  (() (listof Doc?) . ->* . (Doc?)))
                    (<$$> (() (listof Doc?) . ->* . (Doc?))))
  ;(provide <> <+> </> <//> <$> <$$>)
  (provide/contract (lparen Doc?)
                    (rparen Doc?)
                    (lbrace Doc?)
                    (rbrace Doc?)
                    (lbracket Doc?)
                    (rbracket Doc?))
  ;(provide lparen rparen lbrace rbrace lbracket rbracket)
  (provide/contract (squote Doc?)
                    (dquote Doc?)
                    (semi Doc?)
                    (colon Doc?)
                    (comma Doc?)
                    (space Doc?)
                    (dot Doc?)
                    (backslash Doc?)
                    (equals Doc?)
                    (ellipsis Doc?))
  ;(provide squote dquote semi colon comma space dot backslash equals ellipsis)
  ; squotes dquotes braces parens angles brackets enclose

  (provide/contract (sep      ((listof Doc?) . -> . Doc?))
                    (fill-sep ((listof Doc?) . -> . Doc?))
                    (hsep     ((listof Doc?) . -> . Doc?))
                    (vsep     ((listof Doc?) . -> . Doc?)))
  (provide/contract (cat      ((listof Doc?) . -> . Doc?))
                    (fill-cat ((listof Doc?) . -> . Doc?))
                    (hcat     ((listof Doc?) . -> . Doc?))
                    (vcat     ((listof Doc?) . -> . Doc?)))
  (provide/contract (string->doc (string? . -> . Doc?))
                    (value->doc  (any/c . -> . Doc?)))
  (provide with-output-to-string))
