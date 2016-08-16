#lang typed/racket/base

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
           racket/runtime-path)
  (provide (struct-out list-instance))

  (define-runtime-path libz3-path
    (case (system-type 'os)
      [(unix) "libz3.so"]
      [(windows) "z3.dll"]
      [(macosx) "libz3.dylib"]))

  (define libz3
    (let ([libz3-without-suffix (path-replace-extension libz3-path "")])
      (ffi-lib libz3-without-suffix)))

  (define-cpointer-type _z3-config)  (provide z3-config?)
  (define-cpointer-type _z3-context) (provide z3-context?)

  ;; Indicates an instance of a List (e.g. List Int) .
  (struct list-instance (sort nil is-nil cons is-cons head tail) #:transparent)

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


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Low-level bindings
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define-cpointer-type _z3-solver     ) (provide z3-solver?)
  (define-cpointer-type _z3-symbol     ) (provide z3-symbol?)
  (define-cpointer-type _z3-ast        ) (provide z3-ast?)
  (define-cpointer-type _z3-sort       ) (provide z3-sort?)
  (define-cpointer-type _z3-app        ) (provide z3-app?)
  (define-cpointer-type _z3-func-decl  ) (provide z3-func-decl?)
  (define-cpointer-type _z3-constructor) (provide z3-constructor?)
  (define-cpointer-type _z3-pattern    ) (provide z3-pattern?)
  (define-cpointer-type _z3-model      ) (provide z3-model?)
  (define z3-null #f)
  (define z3-null? not)
  (provide z3-null z3-null?)

  ;; Enumerations
  (define _z3-lbool (_enum '(false = -1 undef true) _int32))
  (define _z3-sat-lbool (_enum '(unsat = -1 unknown sat) _int32))
  (define _z3-ast-kind (_enum '(numeral app var quantifier unknown = 1000) _int32))
  (define _z3-error-code (_enum '(ok sort-error iob invalid-arg parser-error
                                     no-parser invalid-pattern memout-fail
                                     file-access-error invalid-usage
                                     internal-fatal dec-ref-error) _int32))

  (define _z3-error-handler (_fun #:keep #t _int -> _void))

  (defz3 toggle-warning-messages! : _bool -> _void)

  ;; Deallocators
  (defz3 del-config  : _z3-config  -> _void)
  (defz3 del-context : _z3-context -> _void)

  (defz3 global-param-set! : _string _string -> _void)
  (defz3 global-param-get : _string
    (val : (_ptr o _string))
    -> (ok? : _bool)
    -> (and ok? val))

  (defz3 mk-config #|#:wrapper (allocator del-config)|# : -> _z3-config)
  (defz3 set-param-value! : _z3-config _string _string -> _void)

  (defz3 mk-context #|#:wrapper (allocator del-context)|# : _z3-config -> _z3-context)
  ;(defz3 update-param-value! : _z3-context _string _string -> _void) ; get Z3 Exception when used
  (defz3 interrupt : _z3-context -> _void)

  ;; Solver API
  (defz3 mk-solver : _z3-context -> _z3-solver)
  (defz3 mk-simple-solver : _z3-context -> _z3-solver)
  (defz3 mk-solver-for-logic : _z3-context _z3-symbol -> _z3-solver)
  ; TODO: mk-solver-from-tactic
  (defz3 solver-get-help : _z3-context _z3-solver -> _string)
  ; TODO: solver-get-param-descrs
  ; TODO: solver-set-params
  (defz3 solver-inc-ref! : _z3-context _z3-solver -> _void)
  (defz3 solver-dec-ref! : _z3-context _z3-solver -> _void)
  (defz3 solver-push! : _z3-context _z3-solver -> _void)
  (defz3 solver-pop! : _z3-context _z3-solver _uint -> _void)
  (defz3 solver-reset! : _z3-context _z3-solver -> _void)
  ; TODO: solver-get-num-scopes
  (defz3 solver-assert! : _z3-context _z3-solver _z3-ast -> _void)
  (defz3 solver-assert-and-track! : _z3-context _z3-solver _z3-ast _z3-ast -> _void)
  ; TODO: solver-get-assertions
  (defz3 solver-check : _z3-context _z3-solver -> _z3-lbool)
  ; TODO: solver-check-assumptions
  (defz3 solver-get-model : _z3-context _z3-solver -> _z3-model)
  ; TODO: solver-get-proof, solver-get-unsat-core
  (defz3 solver-get-reason-unknown : _z3-context _z3-solver -> _string)
  ; TODO: solver-get-statistics
  (defz3 solver-to-string : _z3-context _z3-solver -> _string)

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
    (list-instance res
                   nil-decl
                   is-nil-decl
                   cons-decl
                   is-cons-decl
                   head-decl
                   tail-decl))

  (defz3 mk-true : _z3-context -> _z3-ast)
  (defz3 mk-false : _z3-context -> _z3-ast)
  (defz3 mk-eq : _z3-context _z3-ast _z3-ast -> _z3-ast)

  (define-nary mk-distinct : _z3-ast -> _z3-ast)

  (define-nary mk-pattern : _z3-ast -> _z3-pattern)

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
  (defz3 mk-power : _z3-context _z3-ast _z3-ast -> _z3-ast)
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
  (defz3 ast-to-string : _z3-context _z3-ast -> _string)
  (defz3 model-to-string : _z3-context _z3-model -> _string)
  (defz3 sort-to-string : _z3-context _z3-sort -> _string)
  (defz3 func-decl-to-string : _z3-context _z3-func-decl -> _string)

  ;; error handling functions
  (defz3 get-error-code : _z3-context -> _z3-error-code)
  (defz3 get-error-msg : _z3-error-code -> _string)

  ;; TODO tmp hacks
  (begin
    (define z3-get-sort
      (get-ffi-obj "Z3_get_sort" libz3 (_fun _z3-context _z3-ast -> _z3-sort)))
    (provide z3-get-sort))

  (defz3 get-ast-kind : _z3-context _z3-ast -> _z3-ast-kind)
  (defz3 get-numeral-string : _z3-context _z3-ast -> _string)
  (defz3 to-app : _z3-context _z3-ast -> _z3-app)
  (defz3 get-app-num-args : _z3-context _z3-app -> _uint)
  (defz3 app-to-ast : _z3-context _z3-app -> _z3-ast)
  (defz3 get-app-decl : _z3-context _z3-app -> _z3-func-decl)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Type bindings for low-level Z3 API
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(module z3-ffi-typed typed/racket/base
  (require racket/match)
  (provide (all-defined-out))
  
  (define-type Z3:LBool (U 'false 'undef 'true))
  (define-type Z3:Sat-LBool (U 'unsat 'unknown 'sat))
  (define-type Z3:Ast-Kind (U 'numeral 'app 'var 'quantifier 'unknown))
  (define-type Z3:Error-Code (U 'ok 'sort-error 'iob 'invalid-arg 'parser-error
                                'no-parser 'invalid-pattern 'memout-fail
                                'file-access-error 'invalid-usage
                                'internal-fatal 'dec-ref-error))
  (define-type Global-Param
    (U "auto_config"
       "debug_ref_count"
       "dump_models"
       "memory_high_watermark"
       "memory_max_alloc_count"
       "memory_max_size"
       "model"
       "model_validate"
       "proof"
       "rlimit"
       "smtlib2_compliant"
       "timeout"
       "trace"
       "trace_file_name"
       "type_check"
       "unsat_core"
       "verbose"
       "warning"
       "well_sorted_check"))

  (require/typed/provide (submod ".." z3-ffi)
    [#:opaque Z3:Config  z3-config?]
    [#:opaque Z3:Context z3-context?]
    [#:opaque Z3:Solver      z3-solver?]
    [#:opaque Z3:Func-Decl   z3-func-decl?]
    [#:opaque Z3:Symbol      z3-symbol?]
    [#:opaque Z3:Ast         z3-ast?]
    [#:opaque Z3:Sort        z3-sort?]
    [#:opaque Z3:App         z3-app?]
    [#:opaque Z3:Constructor z3-constructor?]
    [#:opaque Z3:Pattern     z3-pattern?]
    [#:opaque Z3:Model       z3-model?]
    [#:opaque Z3:Null        z3-null?]
    [#:struct list-instance ([sort : Z3:Sort]
                             [nil : Z3:Func-Decl]
                             [is-nil : Z3:Func-Decl]
                             [cons : Z3:Func-Decl]
                             [is-cons : Z3:Func-Decl]
                             [head : Z3:Func-Decl]
                             [tail : Z3:Func-Decl])])

  (define-type Z3:Func (Expr * → Z3:Ast))
  (define-type Expr (U Z3:Ast Z3:App Real Symbol))

  (require/typed/provide (submod ".." z3-ffi)
    [toggle-warning-messages! (Boolean → Void)]
    [global-param-set! (Global-Param String → Void)]
    [global-param-get (Global-Param → String)]
    [mk-config (→ Z3:Config)]
    [del-config (Z3:Config → Void)]
    [set-param-value! (Z3:Config String String → Void)]
    [mk-context (Z3:Config → Z3:Context)]
    [del-context (Z3:Context → Void)]
    ;[update-param-value! (Z3:Context String String → Void)]
    [interrupt (Z3:Context → Void)]
    [z3-null Z3:Null]

    [mk-solver (Z3:Context → Z3:Solver)]
    [mk-simple-solver (Z3:Context → Z3:Solver)]
    [mk-solver-for-logic (Z3:Context Z3:Symbol → Z3:Solver)]
    [solver-get-help (Z3:Context Z3:Solver → String)]
    [solver-inc-ref! (Z3:Context Z3:Solver → Void)]
    [solver-dec-ref! (Z3:Context Z3:Solver → Void)]
    [solver-push! (Z3:Context Z3:Solver → Void)]
    [solver-pop! (Z3:Context Z3:Solver Nonnegative-Fixnum -> Void)]
    [solver-reset! (Z3:Context Z3:Solver → Void)]
    [solver-assert! (Z3:Context Z3:Solver Z3:Ast → Void)]
    [solver-assert-and-track! (Z3:Context Z3:Solver Z3:Ast Z3:Ast → Void)]
    [solver-check (Z3:Context Z3:Solver → Z3:LBool)]
    [solver-get-model (Z3:Context Z3:Solver → Z3:Model)]
    [solver-get-reason-unknown (Z3:Context Z3:Solver → String)]
    [solver-to-string (Z3:Context Z3:Solver → String)]
    
    [mk-string-symbol (Z3:Context String → Z3:Symbol)]
    [mk-uninterpreted-sort (Z3:Context Z3:Symbol → Z3:Sort)]
    [mk-bool-sort (Z3:Context → Z3:Sort)]
    [mk-int-sort (Z3:Context → Z3:Sort)]
    [mk-real-sort (Z3:Context → Z3:Sort)]
    [mk-bv-sort (Z3:Context Nonnegative-Fixnum → Z3:Sort)]
    [mk-array-sort (Z3:Context Z3:Sort Z3:Sort → Z3:Sort)]
    [mk-list-sort (Z3:Context Z3:Symbol Z3:Sort → list-instance)]
    [mk-true (Z3:Context → Z3:Ast)]
    [mk-false (Z3:Context → Z3:Ast)]
    [mk-eq (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
    [mk-distinct (Z3:Context Z3:Ast * → Z3:Ast)]
    [mk-pattern (Z3:Context Z3:Ast Z3:Ast * → Z3:Pattern)]
    

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
    [mk-power (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
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
     (Z3:Context Z3:Symbol Z3:Symbol (Listof (List Z3:Symbol (U Z3:Null Z3:Sort) Nonnegative-Fixnum)) → Z3:Constructor)]

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
    [ast-to-string (Z3:Context Z3:Ast → String)]
    [model-to-string (Z3:Context Z3:Model → String)]
    [sort-to-string (Z3:Context Z3:Sort → String)]
    [func-decl-to-string (Z3:Context Z3:Func-Decl → String)]

    ;; error handling functions
    [get-error-code (Z3:Context → Z3:Error-Code)]
    [get-error-msg (Z3:Error-Code → String)]

    ;; FIXME tmp hacks
    [z3-get-sort (Z3:Context Z3:Ast → Z3:Sort)]

    [get-ast-kind (Z3:Context Z3:Ast → Z3:Ast-Kind)]
    [get-numeral-string (Z3:Context Z3:Ast → String)]
    [to-app (Z3:Context Z3:Ast → Z3:App)]
    [get-app-num-args (Z3:Context Z3:App → Nonnegative-Fixnum)]
    [app-to-ast (Z3:Context Z3:App → Z3:Ast)]
    [get-app-decl (Z3:Context Z3:App → Z3:Func-Decl)]
    )
  )

(require racket/match
         'z3-ffi-typed)

(provide (all-defined-out)
         (all-from-out 'z3-ffi-typed))

;; Given an expr, convert it to a Z3 AST. This is a really simple recursive descent parser.
;; PN: This no longer is a parser. It only coerces some base values now
(: expr->_z3-ast : Expr → Z3:Ast)
(define (expr->_z3-ast e)
  ;(displayln (format "IN: ~a" e))
  (define cur-ctx (ctx))
  (define ast
    (let go ([e e])
      (match e
        ; Numerals
        [(? exact-integer? n)
         (mk-numeral cur-ctx (number->string n) (mk-int-sort cur-ctx))]
        [(?  inexact-real? r)
         (mk-numeral cur-ctx (number->string r) (mk-real-sort cur-ctx))]
        ;; Delayed constant
        [(? symbol? x) (get-val x)]
        ; Anything else
        [(? z3-app? e) (app-to-ast cur-ctx e)]
        [(? z3-ast? e) e]
        [_ (error 'expr->_z3-ast "unexpected: ~a" e)])))
  ;(displayln (format "Output: ~a ~a ~a" expr ast (z3:ast-to-string cur-ctx ast)))
  ast)

(: keyword-arg->_z3-param : Keyword (U Boolean Integer String) → (Values String String))
(define (keyword-arg->_z3-param kw kw-arg)
  (define kw-str (assert (regexp-replaces (keyword->string kw) '((#rx"-" "_") (#rx"\\?$" ""))) string?))
  (define kw-arg-str (match kw-arg
                       [#t "true"]
                       [#f "false"]
                       [(? integer?) (number->string kw-arg)]
                       [(? string?) kw-arg]))
  (values kw-str kw-arg-str))

(: mk-func : Z3:Func-Decl Symbol Natural → Z3:Func)
;; Make a 1st order Z3 function out of func-decl
(define (mk-func f-decl name n)
  (λ xs
    (define num-xs (length xs))
    (cond [(= n num-xs)
           (define cur-ctx (ctx))
           (define args (map expr->_z3-ast xs))
           #;(printf "applying ~a to ~a~n"
                     (func-decl-to-string cur-ctx f-decl)
                     (for/list : (Listof Sexp) ([arg args])
                       (define arg-str (ast-to-string cur-ctx arg))
                       (define sort (sort-to-string cur-ctx (z3-get-sort cur-ctx arg)))
                       `(,arg-str : ,sort)))
           (apply mk-app cur-ctx f-decl args)]
          [else
           (error name "expect ~a arguments, given ~a" n num-xs)])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Dynamic parameter stuff
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Z3 context info structure.
(struct Z3-Ctx ([context : Z3:Context]
                [solver : Z3:Solver]
                [vals : (HashTable Symbol Z3:Ast)]
                [funs : (HashTable Symbol Z3:Func)]
                [sorts : (HashTable Symbol Z3:Sort)])
  #:transparent
  #:mutable)

; This must be parameterized every time any syntax is used
(define current-context-info : (Parameterof (Option Z3-Ctx)) (make-parameter #f))

(define (ctx) : Z3:Context (Z3-Ctx-context (assert (current-context-info))))

(define (get-solver) : Z3:Solver (Z3-Ctx-solver (assert (current-context-info))))

;; A symbol table for sorts
(: get-sort : Symbol → (Option Z3:Sort))
(define (get-sort id)
  (hash-ref (Z3-Ctx-sorts (assert (current-context-info))) id #f))

(: new-sort! : Symbol Z3:Sort → Void)
(define (new-sort! id v)
  (define ctx-info (assert (current-context-info)))
  (define sorts (Z3-Ctx-sorts ctx-info))
  (cond [(hash-has-key? sorts id)
         (error 'new-sort! "Defining a pre-existing sort: ~a" id)]
        [else
         (set-Z3-Ctx-sorts! ctx-info (hash-set sorts id v))]))

(: set-val! : Symbol Z3:Ast → Void)
(define (set-val! id v)
  (define ctx-info (assert (current-context-info)))
  (define vals (Z3-Ctx-vals ctx-info))
  (set-Z3-Ctx-vals! ctx-info (hash-set vals id v)))

(: get-val : Symbol → Z3:Ast)
(define (get-val id)
  (define vals (Z3-Ctx-vals (assert (current-context-info))))
  (hash-ref vals id (λ ()
                      (error 'get-val "cannot find `~a` among ~a" id (hash-keys vals)))))

(: set-fun! : Symbol Z3:Func → Void)
(define (set-fun! id v)
  (define ctx-info (assert (current-context-info)))
  (define funs (Z3-Ctx-funs ctx-info))
  (set-Z3-Ctx-funs! ctx-info (hash-set funs id v)))

(: get-fun : Symbol → Z3:Func)
(define (get-fun id)
  (define funs (Z3-Ctx-funs (assert (current-context-info))))
  (hash-ref funs id (λ ()
                      (error 'get-fun "cannot find `~a` among ~a" id (hash-keys funs)))))
