(module semantic-object mzscheme
  (require (lib "class.ss"))
  (require (lib "contract.ss"))
  (require "../lang/to-string.ss")
  (require "class-resolver.ss")

  ;; ===========================================================================
  ;; DATA DEFINITIONS
  ;; ===========================================================================

  ;; TODO: type-check that lookup-type only ever gets passed a type-name

  (define semantic-object<%>
    (interface ()))

  (define package%
    (class* object% (semantic-object<%>)
      (public)
      (init package-name)

      (define name package-name)

      (super-new)))

  (define resolvable<%>
    (interface ()
      resolve-all))

  (define type<%>
    (interface (semantic-object<%> resolvable<%>)))

  (define ground-type%
    (class* object% (semantic-object<%> type<%> to-string<%>)
      (public get-package get-name to-string resolve-all)

      (init package-name type-name)

      (define name type-name)
      (define package
        (delay (lookup-package package-name)))

      (define (get-package)
        (force package))
      (define (get-name)
        name)
      (define (resolve-all) (void))
      (define (to-string)
        (format "~a" name))

      (super-new)))

  (define unknown-type%
    (class ground-type%
      (init package-name type-name)
      (super-make-object package-name type-name)))

  (define primitive-type%
    (class ground-type%
      (init type-name)
      (super-make-object null type-name)))

  (define-syntax define-primitives
    (syntax-rules ()
      [(_ prim ...)
       (begin (begin (define prim (make-object primitive-type% 'prim))
                     (provide/contract (prim (is-a?/c primitive-type%))))
              ...)]))

  (define-primitives byte char double float int long short boolean)

  (define declared-type%
    (class ground-type%
      (public get-modifiers get-interfaces get-elements)
      (override resolve-all)

      (init package-name type-name)
      (init init-modifiers init-interfaces init-elements)

      (define modifiers init-modifiers)
      (define interfaces
        (delay (map lookup-type init-interfaces)))
      (define elements init-elements)

      (define (get-modifiers)
        modifiers)
      (define (get-interfaces)
        (force interfaces))
      (define (get-elements)
        elements)
      (define (resolve-all)
        (get-interfaces)
        (for-each (lambda (elt) (when elt (send elt resolve-all)))
                  (get-elements))
        (void))
      (super-make-object package-name type-name)))

  (define class%
    (class declared-type%
      (public get-super)
      (init package-name type-name)
      (init modifiers interfaces elements)
      (init init-super)
      (define super
        (delay (lookup-type super)))
      (define (get-super)
        (force super))
      (super-make-object package-name type-name modifiers interfaces elements)))

  (define interface%
    (class declared-type%
      (init package-name type-name)
      (init modifiers interfaces elements)
      (super-make-object package-name type-name modifiers interfaces elements)))

  (define array-type%
    (class* object% (type<%> to-string<%>)
      (public get-base-type resolve-all to-string)
      (init init-base-type)

      (define original-base-type init-base-type)
      (define base-type
        (delay (lookup-type init-base-type)))
      (define (get-base-type)
        (force base-type))
      (define (get-dimension)
        (let ([bt (get-base-type)])
          (if (is-a? bt array-type%)
              (add1 (send bt get-dimension))
              1)))
      (define (resolve-all)
        (send (get-base-type) resolve-all))
      (define (to-string)
        (format "~a[]"
                (cond
                  [(is-a? original-base-type to-string<%>)
                   (send original-base-type to-string)]
                  [(type-name? original-base-type)
                   (type-name->string original-base-type)]
                  [else original-base-type])))
      (super-new)))

  (define type-element%
    (class* object% (semantic-object<%> resolvable<%>)
      (public get-name resolve-all)
      (init init-name)
      (define name init-name)
      (define (get-name) name)
      (define (resolve-all) (void))
      (super-new)))

  (define field%
    (class type-element%
      (public get-modifiers get-type)
      (override resolve-all)
      (init name)
      (init init-modifiers init-type)
      (define modifiers init-modifiers)
      (define type
        (delay (lookup-type init-type)))
      (define (get-modifiers) modifiers)
      (define (get-type)
        (force type))
      (define (resolve-all)
        (get-type)
        (void))
      (super-make-object name)))

  (define behavior%
    (class type-element%
      (public get-formals get-exceptions)
      (override resolve-all)
      (init name)
      (init init-formals init-exceptions)
      (define formals
        (delay (map lookup-type init-formals)))
      (define exceptions
        (delay (map lookup-type init-exceptions)))
      (define (get-formals)
        (force formals))
      (define (get-exceptions)
        (force exceptions))
      (define (resolve-all)
        (get-formals)
        (get-exceptions)
        (void))
      (super-make-object name)))

  (define initializer%
    (class type-element%
      (super-make-object #f)))

  (define constructor%
    (class behavior%
      (init name)
      (init formals exceptions)
      (super-make-object name formals exceptions)))

  (define method%
    (class behavior%
      (public get-return-type)
      (override resolve-all)
      (init name)
      (init formals exceptions)
      (init init-return-type)
      (define return-type
        (delay
          (and init-return-type
               (lookup-type init-return-type))))
      (define (get-return-type)
        (force return-type))
      (define (resolve-all)
        (send this get-formals)
        (send this get-exceptions)
        (get-return-type)
        (void))
      (super-make-object name formals exceptions)))

  ;; TODO: make this a type<%>?
  (define inner-type%
    (class type-element%
      (public get-type)
      (override resolve-all)
      (init name)
      (init init-type)
      (define type
        (delay (lookup-type type)))
      (define (get-type)
        (force type))
      (define (resolve-all)
        (get-type)
        (void))
      (super-make-object name)))

  (provide semantic-object<%>
           type<%>
           package%
           ground-type% unknown-type% primitive-type% declared-type% array-type%
           class% interface%
           type-element% field% initializer% behavior% constructor% method%
           inner-type%))
