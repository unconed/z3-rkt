#lang typed/racket/base

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Untyped module bootstrapping base pointer types
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module z3-ffi-bootstrap racket/base
  (provide (all-defined-out))
  (require (for-syntax racket/base)
           ffi/unsafe
           racket/runtime-path)

  (define-runtime-path libz3-path
    (case (system-type 'os)
      [(unix) "libz3.so"]
      [(windows) "z3.dll"]
      [(macosx) "libz3.dylib"]))

  (define libz3
    (let ([libz3-without-suffix (path-replace-extension libz3-path "")])
      (ffi-lib libz3-without-suffix)))

  (define-cpointer-type _z3-config)
  (define-cpointer-type _z3-context)
  (define ptr? cpointer?)
  )

(module z3-ffi-bootstrap-typed typed/racket/base
  (provide (all-defined-out))
  (require (for-syntax racket/base
                       racket/syntax
                       syntax/parse
                       racket/contract)
           racket/match
           syntax/parse/define)
  
  (define-type TODO Any)

  (require/typed/provide (submod ".." z3-ffi-bootstrap)
    [#:opaque Z3:Config z3-config?]
    [#:opaque Z3:Context z3-context?]
    [#:opaque Ptr ptr?])

  ;; We wrap all our pointers up with a z3-boxed-pointer. This serves two purposes:
  ;; - we hold a strong ref to the context so that it doesn't get GC'd
  ;;   PN: really? Doesn't parameter reference `(current-context-info)` prevent GC?
  ;;   PN: ok, probably something about GC moving pointers around. I'm not touching this for now.
  ;; - we can attach pretty printers and other helpful utilities
  ;; TODO: probably no need to expose this struct. Especially not typed
  (struct z3-boxed-pointer ([ctx : Z3:Context] [ptr : Ptr]) #:transparent)
  
  (: z3-boxed-pointer/c : (Any → Boolean) → Any → Boolean)
  (define (z3-boxed-pointer/c p?)
    (match-lambda
      [(z3-boxed-pointer _ x) (p? x)]
      [_ #f]))

  (: keyword-arg->_z3-param :
     Keyword (U Boolean Number String) → (Values (U String Bytes) String))
  (define (keyword-arg->_z3-param kw kw-arg)
    (define kw-str (regexp-replaces (keyword->string kw) '((#rx"-" "_") (#rx"\\?$" ""))))
    (define kw-arg-str (match kw-arg
                         [#t "true"]
                         [#f "false"]
                         [(? number?) (number->string kw-arg)]
                         [(? string?) kw-arg]))
    (values kw-str kw-arg-str))

  ;; Z3 context info structure.
  (struct z3ctx ([context       : Z3:Context]
                 [vals          : (HashTable Symbol TODO)]
                 [funs          : (HashTable Symbol TODO)]
                 [sorts         : (HashTable Symbol TODO)]
                 [current-model : (Boxof (Option TODO))])
    #:transparent)

  ; This must be parameterized every time any syntax is used
  (define current-context-info : (Parameterof (Option z3ctx)) (make-parameter #f))

  (define (ctx) : Z3:Context
    (z3ctx-context (assert (current-context-info))))

  ;; A symbol table for sorts
  (: get-sort : Symbol → (Option TODO))
  (define (get-sort id)
    (hash-ref (z3ctx-sorts (assert (current-context-info))) id #f))
  (: new-sort! : Symbol TODO → Void)
  (define (new-sort! id v)
    (define sorts (z3ctx-sorts (assert (current-context-info))))
    (cond [(hash-has-key? sorts id)
           (error 'new-sort! "Defining a pre-existing sort: ~a" id)]
          [else (hash-set! sorts id v)]))

  (: set-value! : Symbol TODO → Void)
  (define (set-value! id v)
    (hash-set! (z3ctx-vals (assert (current-context-info))) id v))
  (: get-value : Symbol → TODO)
  (define (get-value id)
    (hash-ref (z3ctx-vals (assert (current-context-info))) id))

  (: set-fun! : Symbol TODO → Void)
  (define (set-fun! id v)
    (hash-set! (z3ctx-vals (assert (current-context-info))) id v))
  (: get-value : Symbol → TODO)
  (define (get-fun id)
    (hash-ref (z3ctx-vals (assert (current-context-info))) id))

  ;; The current model for this context. This is a mutable box.
  (: get-current-model : → TODO)
  (define (get-current-model)
    (cond
      [(unbox (z3ctx-current-model (assert (current-context-info)))) => values]
      [else (error 'get-current-model "No model found")]))
  (: set-current-model! : TODO → Void)
  (define (set-current-model! new-model)
    (set-box! (z3ctx-current-model (assert (current-context-info))) new-model))

  ;; Indicates an instance of a datatype (e.g. (List Int) for List).
  (struct datatype-instance ([z3-sort : TODO] [fns : (HashTable Symbol TODO)]) #:transparent)

  ;; A complex sort (e.g. List) has data about the base sort, a creator function
  ;; (which takes the base sort and a list of sort parameters to apply and produces
  ;; an immutable datatype-instance. We also want to cache instances for specific sort
  ;; parameters (so (List Int) followed by (List Int) should return the same
  ;; datatype-instance.
  (struct z3-complex-sort ([base-sort : TODO]
                           [creator : (TODO (Listof TODO) → datatype-instance)]
                           [instance-hash : (HashTable (Listof TODO) datatype-instance)])
    #:transparent)

  ;; Given a base sort and parameter sorts, get or create a parameterized
  ;; datatype.
  (: get-or-create-instance : TODO (Listof TODO) → datatype-instance)
  (define (get-or-create-instance sort params)
    (match-define (z3-complex-sort base creator cache) sort)
    (hash-ref! cache params (λ () (creator base params))))
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Untyped module for low-level Z3 API
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(module z3-ffi racket/base
  (require (for-syntax racket/base
                       racket/syntax
                       syntax/parse)
           racket/match
           ffi/unsafe
           ffi/unsafe/alloc
           (only-in (submod ".." z3-ffi-bootstrap) libz3 _z3-config _z3-context)
           (submod ".." z3-ffi-bootstrap-typed))

  (struct z3-func-decl-pointer z3-boxed-pointer ()
    #:property prop:procedure (λ (f . args) (apply mk-app (ctx) f (map expr->_z3-ast args)))
    #:transparent)
  
  (define-syntax (define-z3-type stx)
    (syntax-parse stx
      [(_ _t:id
          (~optional ptr-tag    #:defaults ([(ptr-tag    0) #'#f]))
          (~optional ptr-struct #:defaults ([(ptr-struct 0) #'z3-boxed-pointer])))
       (with-syntax ([t?
                      (let* ([s (symbol->string (syntax->datum #'_t))]
                             [t (substring s 1 (string-length s))])
                        (format-id #'_t "~a?" t))])
         #'(begin
             (define-cpointer-type _t #f
               z3-boxed-pointer-ptr
               (λ (ptr)
                 (when ptr-tag
                   (cpointer-push-tag! ptr ptr-tag))
                 (ptr-struct (ctx) ptr)))
             (define p? (z3-boxed-pointer/c t?))
             (provide (rename-out [p? t?]))))]))

  (define-syntax defz3
    (syntax-rules (:)
      [(_ x : t ...)
       (defz3 x #:wrapper values : t ...)]
      [(_ x #:wrapper w : t ...)
       (begin
         (define x
           (let* ([c-name (regexp-replaces (format "Z3_~a" 'x) '((#rx"-" "_") (#rx"!$" "")))]
                  [func (get-ffi-obj c-name libz3 (_fun t ...))])
             (w func)))
         (provide x))]))

  ;; Helper macro to define n-ary AST functions
  (define-syntax define-nary
    (syntax-rules (: ->)
      [(_ fn : argtype -> rettype)
       (defz3 fn : (ctx . args) ::
         (ctx : _z3-context)
         (_uint = (length args))
         (args : (_list i argtype)) -> rettype)]))

  ;; Given an expr, convert it to a Z3 AST. This is a really simple recursive descent parser.
  (define (expr->_z3-ast e)
    ;(displayln (format "IN: ~a" e))
    (define cur-ctx (ctx))
    (define ast
      (let go ([e e])
        (match e
          ; Numerals
          [(? exact-integer? n) (mk-numeral cur-ctx (number->string n) (get-sort 'Int))]
          [(?  inexact-real? r) (mk-numeral cur-ctx (number->string r) (get-sort 'Real))]
          ; Booleans
          [#t (get-value 'true)]
          [#f (get-value 'false)]
          ; Symbols
          [(? symbol? s) (get-value s)]
          ; Anything else
          [_ e])))
    ;(displayln (format "Output: ~a ~a ~a" expr ast (z3:ast-to-string cur-ctx ast)))
    ast)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Low-level bindings
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define-z3-type _z3-symbol)
  (define-z3-type _z3-ast)
  (define-z3-type _z3-sort z3-ast-tag)
  (define-z3-type _z3-app z3-ast-tag)
  (define-z3-type _z3-func-decl z3-ast-tag z3-func-decl-pointer)
  (define-z3-type _z3-constructor)
  (define-z3-type _z3-pattern)
  (define-z3-type _z3-model)

  (define (-z3-null) (z3-boxed-pointer (ctx) #f))
  (define z3-null? (z3-boxed-pointer/c not))
  (provide -z3-null z3-null?)

  ;; Enumerations
  (define _z3-lbool (_enum '(false = -1 undef true) _int32))
  (define _z3-sat-lbool (_enum '(unsat = -1 unknown sat) _int32))
  (define _z3-ast-kind (_enum '(numeral app var quantifier unknown = 1000) _int32))
  (define _z3-error-code (_enum '(ok sort-error iob invalid-arg parser-error
                                     no-parser invalid-pattern memout-fail
                                     file-access-error invalid-usage
                                     internal-fatal dec-ref-error) _int32))

  (define _z3-error-handler (_fun #:keep #t _int -> _void))

  ;; Deallocators
  (defz3 del-config  : _z3-config  -> _void)
  (defz3 del-context : _z3-context -> _void)
  (defz3 del-model   : _z3-context _z3-model -> _void)

  (defz3 mk-config #:wrapper (allocator del-config) : -> _z3-config)
  (defz3 set-param-value! : _z3-config _string _string -> _void)

  (defz3 mk-context #:wrapper (allocator del-context) : _z3-config -> _z3-context)

  (defz3 set-logic : _z3-context _string -> _bool)

  (defz3 mk-string-symbol : _z3-context _string -> _z3-symbol)
  (defz3 mk-uninterpreted-sort : _z3-context _z3-symbol -> _z3-sort)
  (defz3 mk-bool-sort : _z3-context -> _z3-sort)
  (defz3 mk-int-sort : _z3-context -> _z3-sort)
  (defz3 mk-real-sort : _z3-context -> _z3-sort)
  (defz3 mk-bv-sort : _z3-context _uint -> _z3-sort)
  (defz3 mk-array-sort : _z3-context _z3-sort _z3-sort -> _z3-sort)

  (defz3 mk-list-sort : _z3-context _z3-symbol _z3-sort
    (nil-decl : (_ptr o _z3-func-decl))
    (is-nil-decl : (_ptr o _z3-func-decl))
    (cons-decl : (_ptr o _z3-func-decl))
    (is-cons-decl : (_ptr o _z3-func-decl))
    (head-decl : (_ptr o _z3-func-decl))
    (tail-decl : (_ptr o _z3-func-decl))
    -> (res : _z3-sort) ->
    (datatype-instance res (hasheq 'nil nil-decl
                                   'is-nil is-nil-decl
                                   'cons cons-decl
                                   'is-cons is-cons-decl
                                   'head head-decl
                                   'tail tail-decl)))

  (defz3 mk-true : _z3-context -> _z3-ast)
  (defz3 mk-false : _z3-context -> _z3-ast)
  (defz3 mk-eq : _z3-context _z3-ast _z3-ast -> _z3-ast)

  (define-nary mk-distinct : _z3-ast -> _z3-ast)

  ;; Boolean operations
  (defz3 mk-not : _z3-context _z3-ast -> _z3-ast)
  (defz3 mk-ite : _z3-context _z3-ast _z3-ast _z3-ast -> _z3-ast)
  (defz3 mk-iff : _z3-context _z3-ast _z3-ast -> _z3-ast)
  (defz3 mk-implies : _z3-context _z3-ast _z3-ast -> _z3-ast)
  (defz3 mk-xor : _z3-context _z3-ast _z3-ast -> _z3-ast)
  (define-nary mk-and : _z3-ast -> _z3-ast)
  (define-nary mk-or : _z3-ast -> _z3-ast)

  ;; Arithmetic operations
  (define-nary mk-add : _z3-ast -> _z3-ast)
  (define-nary mk-mul : _z3-ast -> _z3-ast)
  (define-nary mk-sub : _z3-ast -> _z3-ast)
  (defz3 mk-div : _z3-context _z3-ast _z3-ast -> _z3-ast)
  (defz3 mk-mod : _z3-context _z3-ast _z3-ast -> _z3-ast)
  (defz3 mk-rem : _z3-context _z3-ast _z3-ast -> _z3-ast)
  (defz3 mk-is-int : _z3-context _z3-ast -> _z3-ast)

  ;; Comparisons
  (defz3 mk-lt : _z3-context _z3-ast _z3-ast -> _z3-ast)
  (defz3 mk-le : _z3-context _z3-ast _z3-ast -> _z3-ast)
  (defz3 mk-gt : _z3-context _z3-ast _z3-ast -> _z3-ast)
  (defz3 mk-ge : _z3-context _z3-ast _z3-ast -> _z3-ast)

  ;; Numerals
  (defz3 mk-numeral : _z3-context _string _z3-sort -> _z3-ast)

  ;; Uninterpreted constants, functions and applications
  (defz3 mk-fresh-func-decl : (ctx prefix domain range) ::
    (ctx : _z3-context)
    (prefix : _string)
    (_uint = (length domain))
    (domain : (_list i _z3-sort))
    (range : _z3-sort)
    -> _z3-func-decl)

  (defz3 mk-app : (ctx d . args) ::
    (ctx : _z3-context)
    (d : _z3-func-decl)
    (_uint = (length args))
    (args : (_list i _z3-ast)) -> _z3-ast)

  (defz3 mk-fresh-const : _z3-context _string _z3-sort -> _z3-app)

  ;; Array operations
  (defz3 mk-select : _z3-context _z3-ast _z3-ast -> _z3-ast)
  (defz3 mk-store : _z3-context _z3-ast _z3-ast _z3-ast -> _z3-ast)

  ;; Complex types
  (defz3 mk-constructor :
    (ctx name recognizer names-sorts-refs) ::
    (ctx         : _z3-context)
    (name        : _z3-symbol)
    (recognizer  : _z3-symbol)
    (num-fields  : _uint = (length names-sorts-refs))
    (field-names : (_list i _z3-symbol) = (map car names-sorts-refs))
    (sorts       : (_list i _z3-sort/null) = (map cadr names-sorts-refs))
    (sort-refs   : (_list i _uint) = (map caddr names-sorts-refs))
    -> _z3-constructor)

  (defz3 query-constructor :
    (ctx constructor num-fields) ::
    (ctx            : _z3-context)
    (constructor    : _z3-constructor)
    (num-fields     : _uint)
    (constructor-fn : (_ptr o _z3-func-decl))
    (tester-fn      : (_ptr o _z3-func-decl))
    (accessor-fns   : (_list o _z3-func-decl num-fields))
    -> _void ->
    (values constructor-fn tester-fn accessor-fns))

  (defz3 mk-datatype :
    (ctx name constructors) ::
    (ctx : _z3-context)
    (name : _z3-symbol)
    (_uint = (length constructors))
    (constructors : (_list i _z3-constructor))
    -> _z3-sort)

  ;; Quantifiers
  (defz3 mk-forall-const :
    (ctx weight bound-consts patterns body) ::
    (ctx : _z3-context)
    (weight : _uint)
    (_uint = (length bound-consts))
    (bound-consts : (_list i _z3-app))
    (_uint = (length patterns))
    (patterns : (_list i _z3-pattern))
    (body : _z3-ast)
    -> _z3-ast)
  (defz3 mk-exists-const :
    (ctx weight bound-consts patterns body) ::
    (ctx : _z3-context)
    (weight : _uint)
    (_uint = (length bound-consts))
    (bound-consts : (_list i _z3-app))
    (_uint = (length patterns))
    (patterns : (_list i _z3-pattern))
    (body : _z3-ast)
    -> _z3-ast)

  ;; -> string functions
  (defz3 context-to-string : _z3-context -> _string)
  (defz3 ast-to-string : _z3-context _z3-ast -> _string)
  (defz3 model-to-string : _z3-context _z3-model -> _string)
  (defz3 sort-to-string : _z3-context _z3-sort -> _string)
  (defz3 func-decl-to-string : _z3-context _z3-func-decl -> _string)

  ;; error handling functions
  (defz3 get-error-code : _z3-context -> _z3-error-code)
  (defz3 get-error-msg : _z3-error-code -> _string)

  (defz3 assert-cnstr : _z3-context _z3-ast -> _void)
  (defz3 check : _z3-context -> _z3-sat-lbool)
  (defz3 check-and-get-model : _z3-context (model : (_ptr o (_or-null _z3-model))) -> (rv : _z3-sat-lbool) -> (values rv model))
  (defz3 eval : _z3-context _z3-model _z3-ast (v : (_ptr o (_or-null _z3-ast))) -> (rv : _bool) -> (values rv v))
  (defz3 get-ast-kind : _z3-context _z3-ast -> _z3-ast-kind)
  (defz3 get-numeral-string : _z3-context _z3-ast -> _string)
  (defz3 to-app : _z3-context _z3-ast -> _z3-app)
  (defz3 get-app-num-args : _z3-context _z3-app -> _uint)
  (defz3 get-app-decl : _z3-context _z3-app -> _z3-func-decl)
  )

(module z3-ffi-typed typed/racket/base
  (require (submod ".." z3-ffi-bootstrap-typed))
  (provide (all-from-out (submod ".." z3-ffi-bootstrap-typed))
           (all-defined-out))
  
  (define-type Z3:LBool (U #f 'undef #t))
  (define-type Z3:Sat-LBool (U 'unsat 'unknown 'sat))
  (define-type Z3:Ast-Kind (U 'numeral 'app 'var 'quantifier 'unknown))
  (define-type Z3:Error-Code (U 'ok 'sort-error 'iob 'invalid-arg 'parser-error
                                'no-parser 'invalid-pattern 'memout-fail
                                'file-access-error 'invalid-usage
                                'internal-fatal 'dec-ref-error))

  (require/typed/provide (submod ".." z3-ffi)
    [#:opaque Z3:Symbol      z3-symbol?]
    [#:opaque Z3:Ast         z3-ast?]
    [#:opaque Z3:Sort        z3-sort?]
    [#:opaque Z3:App         z3-app?]
    [#:opaque Z3:Func-Decl   z3-func-decl?]
    [#:opaque Z3:Constructor z3-constructor?]
    [#:opaque Z3:Pattern     z3-pattern?]
    [#:opaque Z3:Model       z3-model?]
    [#:opaque Z3:Null        z3-null?]

    
    [mk-config (→ Z3:Config)]
    [set-param-value! (Z3:Config String String → Void)]
    [mk-context (Z3:Config → Z3:Context)]
    [set-logic (Z3:Context String → Boolean)]
    
    [mk-string-symbol (Z3:Context String → Z3:Symbol)]
    [mk-uninterpreted-sort (Z3:Context Z3:Symbol → Z3:Sort)]
    [mk-bool-sort (Z3:Context → Z3:Sort)]
    [mk-int-sort (Z3:Context → Z3:Sort)]
    [mk-real-sort (Z3:Context → Z3:Sort)]
    [mk-bv-sort (Z3:Context Nonnegative-Fixnum → Z3:Sort)]
    [mk-array-sort (Z3:Context Z3:Sort Z3:Sort → Z3:Sort)]
    [mk-list-sort (Z3:Context Z3:Symbol Z3:Sort → TODO)]
    [mk-true (Z3:Context → Z3:Ast)]
    [mk-false (Z3:Context → Z3:Ast)]
    [mk-eq (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]

    [mk-distinct (Z3:Context Z3:Ast * → Z3:Ast)]

    ;; Boolean operations
    [mk-not (Z3:Context Z3:Ast → Z3:Ast)]
    [mk-ite (Z3:Context Z3:Ast Z3:Ast Z3:Ast → Z3:Ast)]
    [mk-iff (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
    [mk-implies (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
    [mk-xor (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
    [mk-and (Z3:Context Z3:Ast * → Z3:Ast)]
    [mk-or (Z3:Context Z3:Ast * → Z3:Ast)]

    ;; Arithmetic operations
    [mk-add (Z3:Context Z3:Ast * → Z3:Ast)]
    [mk-mul (Z3:Context Z3:Ast * → Z3:Ast)]
    [mk-sub (Z3:Context Z3:Ast * → Z3:Ast)]
    [mk-div (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
    [mk-mod (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
    [mk-rem (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
    [mk-is-int (Z3:Context Z3:Ast → Z3:Ast)]

    ;; Comparisons
    [mk-lt (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
    [mk-le (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
    [mk-gt (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
    [mk-ge (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]

    ;; Numerals
    [mk-numeral (Z3:Context String Z3:Sort → Z3:Ast)]

    ;; Uninterpreted constants, functions and applications
    [mk-fresh-func-decl (Z3:Context String (Listof Z3:Sort) Z3:Sort → Z3:Func-Decl)]
    [mk-app (Z3:Context Z3:Func-Decl Z3:Ast * → Z3:Ast)]
    [mk-fresh-const (Z3:Context String Z3:Sort → Z3:App)]

    ;; Array operations
    [mk-select (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
    [mk-store (Z3:Context Z3:Ast Z3:Ast Z3:Ast → Z3:Ast)]

    ;; Complex types
    [mk-constructor
     (Z3:Context Z3:Symbol Z3:Symbol (Listof (List Z3:Symbol (Option Z3:Sort) Nonnegative-Fixnum)) → Z3:Constructor)]

    [query-constructor
     (Z3:Context Z3:Constructor Nonnegative-Fixnum →
                 (Values Z3:Func-Decl Z3:Func-Decl (Listof Z3:Func-Decl)))]

    [mk-datatype (Z3:Context Z3:Symbol (Listof Z3:Constructor) → Z3:Sort)]

    ;; Quantifiers
    [mk-forall-const
     (Z3:Context Nonnegative-Fixnum (Listof Z3:App) (Listof Z3:Pattern) Z3:Ast → Z3:Ast)]
    [mk-exists-const
     (Z3:Context Nonnegative-Fixnum (Listof Z3:App) (Listof Z3:Pattern) Z3:Ast → Z3:Ast)]

    ;; → string functions
    [context-to-string (Z3:Context → String)]
    [ast-to-string (Z3:Context Z3:Ast → String)]
    [model-to-string (Z3:Context Z3:Model → String)]
    [sort-to-string (Z3:Context Z3:Sort → String)]
    [func-decl-to-string (Z3:Context Z3:Func-Decl → String)]

    ;; error handling functions
    [get-error-code (Z3:Context → Z3:Error-Code)]
    [get-error-msg (Z3:Error-Code → String)]

    [assert-cnstr (Z3:Context Z3:Ast → Void)]
    [check (Z3:Context → Z3:Sat-LBool)]
    [check-and-get-model (Z3:Context → (Values Z3:Sat-LBool (Option Z3:Model)))]
    [eval (Z3:Context Z3:Model Z3:Ast → (Values Boolean (Option Z3:Ast)))]
    [get-ast-kind (Z3:Context Z3:Ast → Z3:Ast-Kind)]
    [get-numeral-string (Z3:Context Z3:Ast → String)]
    [to-app (Z3:Context Z3:Ast → Z3:App)]
    [get-app-num-args (Z3:Context Z3:App → Nonnegative-Fixnum)]
    [get-app-decl (Z3:Context Z3:App → Z3:Func-Decl)]
    ))
