
(module jcode mzscheme
  (require (lib "mrpict.ss" "texpict")
           (lib "class.ss")
           (lib "mred.ss" "mred")
           (lib "contract.ss")
           ;"../util/run-mrpict-talk.scm"
           )
  
  (provide/contract
   (jcode (->* ()
               (listof (union string? (list/c string? string?)))
               (pict?)))
   (jcode/subs (->* ()
                    (listof (union string? (list/c string? string?)))
                    (pict? (listof pict?))))
   (jprogram-text-size number?))

  (provide regexp-table
           color-entry-used
           color-entry-regexps
           color-table)
  
  (define exponent-color "blue")
  (define jprogram-text-size 30)
  (define small-program-text-size 24)
  
  (define-struct line (pict subpicts))
  
  ;; color-table : (parameter (listof (cons (union (instanceof color%) string) (listof string))))
  ;; specifies the text to be colored in the code examples.
  ;; the first string in each list is the color and the
  ;; other strings are keys that identify colorable bits of the
  ;; syntax.
  (define color-table (make-parameter '()))
  
  (define (make-turnstyle size)
    (let* ([pict (text "X" 'modern size)]
           [w (pict-width pict)]
           [h (floor (* 2/3 (pict-height pict)))])
      (dc
       (lambda (dc dx dy)
         (let ([old-pen (send dc get-pen)])
           (send dc set-pen (send the-pen-list find-or-create-pen "black" (round (/ size 12)) 'solid))
           (send dc draw-line dx dy dx (+ dy h))
           (send dc draw-line dx (+ dy (quotient h 2)) (+ dx w) (+ dy (quotient h 2)))
           (send dc set-pen old-pen)))
       w h 0 0)))

  ;; the regexp for characters that must preceed of suceed 
  ;; a match in the color table
  (define sep-chars "[]\\-\\[ /!;{}(),.*\t+]")
  
  ;; escape-regexp-specials : string -> string
  ;; adds backslash character in front of each
  ;; special regexp character.
  (define (escape-regexp-specials str)
    (apply
     string
     (let loop ([chars (string->list str)])
       (cond
         [(null? chars) null]
         [else
          (let ([char (car chars)])
            (case (car chars)
              [(#\( #\) #\. #\* #\+ #\? #\[ #\] #\. #\^ #\\ #\|)
               (list* #\\ (car chars) (loop (cdr chars)))]
              [else
               (cons (car chars) (loop (cdr chars)))]))]))))

  (define-struct color-entry (color/proc regexps used))
  
  ;; like color table, except followed by a list of regexps, not strings.
  (define (compute-regexp-table)
    (map (lambda (color-table-entry)
           (let ([regexps (map (lambda (m)
                                 (regexp (format "^((.*~a)|)(~a)((~a.*)|)$" 
                                                 sep-chars
                                                 (escape-regexp-specials m)
                                                 sep-chars)))
                               (cdr color-table-entry))])
             (make-color-entry
              (car color-table-entry)
              regexps
              (map (lambda (x) (box #f)) regexps))))
         (color-table)))
  
  (define regexp-table
    (let ([t #f])
      (lambda ()
        (unless t (set! t (compute-regexp-table)))
        t)))
  
  ;; jcode : (listof str) *-> pict
  ;; constructs a pict of the input list of strings,
  ;; treating each string as a line in the program
  (define (jcode . x)
    (let ([lines (map line->text x)])
      (apply vl-append (map line-pict lines))))
  
  ;; jcode/subs : (listof str) *-> pict (listof pict)
  ;; constructs a pict of the input list of strings,
  ;; treating each string as a line in the program.
  ;; also returns the @{}@ bracketed portions as
  ;; picts, for purposes of highlighting and such.
  (define (jcode/subs . x)
    (let* ([lines (map line->text x)]
           [main-pict (apply vl-append (map line-pict lines))]
           [subs (apply append (map line-subpicts lines))])
      (values main-pict subs)))
 
  ;; exponented-strings = (listof (union string (make-up exponented-strings)))
  ;; split-out-exponents : string -> exponented-strings
  (define-struct up (expt))
  (define-struct down (expt))
  (define-struct separate (str))
  (define (split-out-exponents str)
    ;; char-stream : -> (union eof char 'open-up 'open-down 'close-up 'close-down)
    (define (stream-next peek?)
      (let ([maybe-inc
             (if peek?
                 void
                 (lambda (n) (set! char-index (+ char-index n))))])
        (lambda ()
          (cond
            [(not (char-index . < . (string-length str))) eof]
            [(and ((+ char-index 1) . < . (string-length str))
                  (char=? (string-ref str char-index) #\^)
                  (char=? (string-ref str (+ char-index 1)) #\{))
             (maybe-inc 2)
             'open-up]
            [(and ((+ char-index 1) . < . (string-length str))
                  (char=? (string-ref str char-index) #\$)
                  (char=? (string-ref str (+ char-index 1)) #\{))
             (maybe-inc 2)
             'open-down]
            [(and ((+ char-index 1) . < . (string-length str))
                  (char=? (string-ref str char-index) #\@)
                  (char=? (string-ref str (+ char-index 1)) #\{))
             (maybe-inc 2)
             'open-separate]
            [(and ((+ char-index 1) . < . (string-length str))
                  (char=? (string-ref str char-index) #\})
                  (char=? (string-ref str (+ char-index 1)) #\^))
             (maybe-inc 2)
             'close-up]
            [(and ((+ char-index 1) . < . (string-length str))
                  (char=? (string-ref str char-index) #\})
                  (char=? (string-ref str (+ char-index 1)) #\$))
             (maybe-inc 2)
             'close-down]
            [(and ((+ char-index 1) . < . (string-length str))
                  (char=? (string-ref str char-index) #\})
                  (char=? (string-ref str (+ char-index 1)) #\@))
             (maybe-inc 2)
             'close-separate]
            [else
             (begin0 (string-ref str char-index)
                     (maybe-inc 1))]))))
    (define char-index 0)
    
    (define get-char (stream-next #f))
    (define peek-char (stream-next #t))
    
    ;; mismatch-deteched
    (define (mismatch-detected reason)
      (error 'split-out-exponents "mismatch detected; ~a at ~a in ~s"
             reason char-index str))

    ;; main-loop : (listof chars) -> exponented-strings
    (define (main-loop)
      (let loop ([acc null])
        (let ([close-up-acc
               (lambda ()
                 (if (null? acc)
                     null
                     (list (apply string (reverse acc)))))])
          (let ([p-char (peek-char)])
            (cond
              [(eof-object? p-char) 
               (get-char)
               (close-up-acc)]
              [else
               (case p-char
                 [(open-up) 
                  (let ([_1 (get-char)]   ;; throw away the open
                        [up (make-up (main-loop))]
                        [close (get-char)])  ;; throw away the close
                    (unless (eq? 'close-up close)
                      (mismatch-detected (format "expected close-up, got ~s" close)))
                    (list* (apply string (reverse acc))
                           up
                           (loop null)))]
                 [(open-down) 
                  (let ([_1 (get-char)]   ;; throw away the open
                        [up (make-down (main-loop))]
                        [close (get-char)])  ;; throw away the close
                    (unless (eq? 'close-down close)
                      (mismatch-detected (format "expected close-down, got ~s" close)))
                    (list* (apply string (reverse acc))
                           up
                           (loop null)))]
                 [(open-separate) 
                  (let ([_1 (get-char)]   ;; throw away the open
                        [up (make-separate (main-loop))]
                        [close (get-char)])  ;; throw away the close
                    (unless (eq? 'close-separate close)
                      (mismatch-detected (format "expected close-separate, got ~s" close)))
                    (list* (apply string (reverse acc))
                           up
                           (loop null)))]
                 [(close-up close-down close-separate) (close-up-acc)]
                 [else
                  (let ([next (get-char)])
                    (loop (cons next acc)))])])))))
    
    (begin0 (main-loop)
            (unless (eof-object? (peek-char))
              (mismatch-detected "got to eof"))))
  
  ;; line->text : (union (list color string) string) -> line
  (define (line->text line/color)
    (let* ([sub-picts null]
           [line (if (string? line/color)
                     line/color
                     (cadr line/color))]
           [line-color (if (string? line/color)
                           "black"
                           (car line/color))]
           [line-pieces (split-out-exponents line)]
           [line-picts
            (let loop ([line-pieces line-pieces]
                       [height 0])
              (cond
                [(null? line-pieces) null]
                [else (let* ([first (car line-pieces)]
                             [factor 1/3]
                             [x-height (pict-height (text "X" 'modern jprogram-text-size))]
                             [combine
                              (lambda (lift/drop to-be-lift/drop-ed)
                                (vc-append
                                 to-be-lift/drop-ed
                                 (blank 0 (floor (* x-height factor)))))]
                             [pict
                              (cond
                                [(up? first)
                                 (let ([super (colorize
                                               (apply
                                                hbl-append
                                                (loop (up-expt first) (+ height 1)))
                                               exponent-color)])
                                   (combine lift super))]
                                [(down? first)
                                 (let ([sub (colorize 
                                             (apply 
                                              hbl-append
                                              (loop (down-expt first) (+ height 1)))
                                             exponent-color)])
                                   (combine drop sub))]
                                [(separate? first)
                                 (let* ([res (loop (separate-str first) height)]
                                        [sep (if (null? res)
                                                 (zero-width-text (height->size height))
                                                 (apply hbl-append res))])
                                   (set! sub-picts (cons sep sub-picts))
                                   sep)]
                                [(string? first)
                                 (let ([split-out (split-up-string first)])
                                   (if (null? split-out)
                                       (zero-width-text (height->size height))
                                       (apply vl-append
                                              (map (lambda (x) 
                                                     (if (= height 0)
                                                         (string->text x (height->size height) #t)
                                                         (string->text x (height->size height) #f)))
                                                   split-out))))])])
                        (cons pict
                              (loop (cdr line-pieces) height)))]))]
           [final-pict (if (null? line-picts)
                           (blank)
                           (colorize (apply hbl-append line-picts) line-color))])
      (for-each (lambda (sub)
                  (find-lt final-pict sub))
                sub-picts)
      (make-line final-pict (reverse sub-picts))))

  (define (zero-width-text size)
    (let ([p (text "yX" 'modern size)])
      (blank 0 (pict-height p))))
  
  ;; height->size : number -> number
  (define (height->size height)
    (cond
      [(zero? height) jprogram-text-size]
      [else small-program-text-size]))
  

  ;; split-up-string : string -> (listof strings)
  ;; splits strings at newline characters
  (define (split-up-string str)
    (let loop ([chars (string->list str)]
               [acc null])
      (cond
        [(null? chars) 
         (if (null? acc)
             null
             (list (apply string (reverse acc))))]
        [else
         (case (car chars)
           [(#\newline) (cons (apply string (reverse acc))
                              (loop (cdr chars) null))]
           [else (loop (cdr chars)
                       (cons (car chars) acc))])])))
  
  ;; string->text : string number boolean -> pict
  ;; constrcts a single pict with the symbols in color table colored
  (define (string->text x size color?)
    (let loop ([program-text x]
               [ct (regexp-table)])
      (cond
        [(null? ct) (text program-text 'modern size)]
        [else 
         (let* ([color-entry (car ct)]
                [regs (color-entry-regexps color-entry)]
                [clr/proc (color-entry-color/proc color-entry)]
                [proc
                 (if (string? clr/proc)
                     (lambda (during size)
                       (let ([p (text during 'modern size)])
                         (if color?
                             (colorize p clr/proc)
                             p)))
                     clr/proc)]
                [matched (match-strings program-text size proc regs (color-entry-used color-entry))])
           (if matched
               (hbl-append
                (loop (car matched) (regexp-table))
                (cadr matched)
                (loop (caddr matched) (regexp-table)))
               (loop program-text (cdr ct))))])))
  
  ;; match-strings : string
  ;;                (pict -> pict) 
  ;;                (cons string (listof string)) 
  ;;                (cons (box boolean) (listof (box boolean))
  ;;             -> (union #f (list string pict string))
  ;; if any strings in matchlist match program-text, color that substring
  ;; the color. If none match, return #f.
  (define (match-strings program-text size do-color match-list boxes)
    (let ([m (ormap
              (lambda (reg b) 
                (let ([m (regexp-match reg program-text)])
                  (if m
                      (begin (set-box! b #t)
                             m)
                      m)))
              match-list
              boxes)])
      (and m 
           (let ([before  (cadr m)]
                 [junk1   (caddr m)]
                 [during  (cadddr m)]
                 [after   (car  (cddddr m))]
                 [junk2   (cadr (cddddr m))])
             (list before
                   (do-color during size)
                   after))))))