#lang racket/base

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         racket/match
         ffi/unsafe
         ffi/unsafe/alloc
         racket/runtime-path
         syntax/parse/define
         racket/splicing)
(provide (struct-out list-instance))

(define libz3
  (let ([lib-name (case (system-type 'os)
                    [(unix) "libz3.so"]
                    [(windows) "z3.dll"]
                    [(macosx) "libz3.dylib"])])
    (define Z3_LIB "Z3_LIB")
    (define libz3-path (getenv Z3_LIB))
    (cond
      [libz3-path
       (define libz3-without-suffix (path-replace-extension (build-path libz3-path lib-name) ""))
       (ffi-lib libz3-without-suffix)]
      [else
       (error 'z3-rkt
              "Cannot locate Z3 libary. Please set ${~a} to the directory containing ~a"
              Z3_LIB
              lib-name)])))

;; Indicates an instance of a List (e.g. List Int) .
(struct list-instance (sort nil is-nil cons is-cons head tail) #:transparent)

(splicing-local
    (
     (define racket->c-regexps
       '((#rx"->" "_to_")
         (#rx"-" "_")
         (#rx"!$" "")
         (#rx"\\?$" "")))
     (define (racket->c-name x)
       (regexp-replaces (format "Z3_~a" x) racket->c-regexps))
     )
  
  (define-syntax define-z3
    (syntax-parser
      #:literals (*) ; TODO: how to have `:` in here?
      [(_ x:id (~literal :) t₀ ... tₙ * -> tₐ)
       (with-syntax ([(x₀ ...)
                      (datum->syntax
                       #f
                       (for/list ([(_ i) (in-indexed (syntax->list #'(t₀ ...)))])
                         (format-id #f "x~a" i)))])
         #'(define-z3 x : (x₀ ... . x*) ::
             (x₀ : t₀) ...
             (_uint = (length x*))
             (x* : (_list i tₙ))
             -> tₐ))]
      [(_ x:id (~literal :) t ...)
       #'(define x (get-ffi-obj (racket->c-name 'x) libz3 (_fun t ...)))]))

  (define-simple-macro (define-z3/provide [x:id (~literal :) t ...] ...)
    (begin (define-z3 x : t ...) ...
           (provide x ...)))

  (define-syntax define-z3-pointer-types/provide-predicates
    (syntax-parser
      [(_ _t:id ...)
       (with-syntax ([(t? ...)
                      (datum->syntax
                       #'(_t ...)
                       (for/list ([_tᵢ (in-list (syntax->list #'(_t ...)))])
                         (define sᵢ
                           (let ([str (symbol->string (syntax-e _tᵢ))])
                             (substring str 1 (string-length str))))
                         (format-id _tᵢ "~a?" sᵢ)))])
         #'(begin
             (define-cpointer-type _t) ...
             (provide t? ...)))])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Low-level bindings
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-z3-pointer-types/provide-predicates
  _z3-config
  _z3-context
  _z3-solver
  _z3-symbol
  _z3-ast
  _z3-sort
  _z3-app
  _z3-func-decl
  _z3-constructor
  _z3-pattern
  _z3-model
  _z3-stats
  _z3-ast-vector
  _z3-constructor-list
  _z3-func-interp
  _z3-func-entry
  _z3-params
  _z3-param-descrs)
(define z3-null #f)
(define z3-null? not)
(provide z3-null z3-null?)

;; Enumerations
(define _z3-lbool (_enum '(false = -1 undef true) _int32))
(define _z3-sat-lbool (_enum '(unsat = -1 unknown sat) _int32))
(define _z3-ast-kind (_enum '(numeral app var quantifier unknown = 1000) _int32))
(define _z3-error-code (_enum '(ok
                                sort-error
                                iob
                                invalid-arg
                                parser-error
                                no-parser
                                invalid-pattern
                                memout-fail
                                file-access-error
                                invalid-usage
                                internal-fatal
                                dec-ref-error
                                z3-exception)
                              _int32))
(define _z3-ast-print-mode (_enum '(print-smtlib-full
                                    print-low-level
                                    print-smtlib-compliant
                                    print-smtlib2-compliant)
                                  _int32))
(define _z3-param-kind (_enum '(uint bool double symbol string other invalid) _int32))

(define-z3/provide
  ;; Deallocators
  [del-config  : _z3-config  -> _void]
  [del-context : _z3-context -> _void]

  [global-param-set! : _string _string -> _void]
  [global-param-get : _string
    (val : (_ptr o _string))
    -> (ok? : _bool)
    -> (and ok? val)]

  [mk-config : -> _z3-config]
  [set-param-value! : _z3-config _string _string -> _void]

  [mk-context : _z3-config -> _z3-context]
  ;(update-param-value! : _z3-context _string _string -> _void) ; get Z3 Exception when used
  [interrupt : _z3-context -> _void]

  ;; Solver API
  [mk-solver : _z3-context -> _z3-solver]
  [mk-simple-solver : _z3-context -> _z3-solver]
  [mk-solver-for-logic : _z3-context _z3-symbol -> _z3-solver]
  ; TODO: mk-solver-from-tactic
  [solver-get-help : _z3-context _z3-solver -> _string]
  [solver-get-param-descrs : _z3-context _z3-solver -> _z3-param-descrs]
  [solver-set-params! : _z3-context _z3-solver _z3-params -> _void]
  [solver-inc-ref! : _z3-context _z3-solver -> _void]
  [solver-dec-ref! : _z3-context _z3-solver -> _void]
  [solver-push! : _z3-context _z3-solver -> _void]
  [solver-pop! : _z3-context _z3-solver _uint -> _void]
  [solver-reset! : _z3-context _z3-solver -> _void]
  [solver-get-num-scopes : _z3-context _z3-solver -> _uint]
  [solver-assert! : _z3-context _z3-solver _z3-ast -> _void]
  [solver-assert-and-track! : _z3-context _z3-solver _z3-ast _z3-ast -> _void]
  [solver-get-assertions : _z3-context _z3-solver -> _z3-ast-vector]
  [solver-check : _z3-context _z3-solver -> _z3-lbool]
  [solver-check-assumptions : (ctx slvr assumptions) ::
    (ctx  : _z3-context)
    (slvr : _z3-solver)
    (num-assumptions : _uint = (length assumptions))
    (assumptions : (_list i _z3-ast))
    -> _z3-lbool]
  [solver-get-model : _z3-context _z3-solver -> _z3-model]
  [solver-get-proof : _z3-context _z3-solver -> _z3-ast]
  [solver-get-unsat-core : _z3-context _z3-solver -> _z3-ast-vector]
  [solver-get-reason-unknown : _z3-context _z3-solver -> _string]
  [solver-get-statistics : _z3-context _z3-solver -> _z3-stats]
  [solver->string : _z3-context _z3-solver -> _string]

  [mk-string-symbol : _z3-context _string -> _z3-symbol]

  ;; Parameters
  [mk-params : _z3-context -> _z3-params]
  [params-inc-ref! : _z3-context _z3-params -> _void]
  [params-dec-ref! : _z3-context _z3-params -> _void]
  [params-set-bool! : _z3-context _z3-params _z3-symbol _bool -> _void]
  [params-set-uint! : _z3-context _z3-params _z3-symbol _uint -> _void]
  [params-set-double! : _z3-context _z3-params _z3-symbol _double -> _void]
  [params-set-symbol! : _z3-context _z3-params _z3-symbol _z3-symbol -> _void]
  [params->string : _z3-context _z3-params -> _string]
  [params-validate! : _z3-context _z3-params _z3-param-descrs -> _void]

  ;; Parameter Descriptions
  [param-descrs-inc-ref! : _z3-context _z3-param-descrs -> _void]
  [param-descrs-dec-ref! : _z3-context _z3-param-descrs -> _void]
  [param-descrs-get-kind : _z3-context _z3-param-descrs _z3-symbol -> _z3-param-kind]
  [param-descrs-size : _z3-context _z3-param-descrs -> _uint]
  [param-descrs-get-name : _z3-context _z3-param-descrs _uint -> _z3-symbol]
  [param-descrs->string : _z3-context _z3-param-descrs -> _string]


  ;; Sorts
  [mk-uninterpreted-sort : _z3-context _z3-symbol -> _z3-sort]
  [mk-bool-sort : _z3-context -> _z3-sort]
  [mk-int-sort : _z3-context -> _z3-sort]
  [mk-real-sort : _z3-context -> _z3-sort]
  [mk-bv-sort : _z3-context _uint -> _z3-sort]
  [mk-array-sort : _z3-context _z3-sort _z3-sort -> _z3-sort]
  ; TODO mk-finite-domain-sort
  ; TODO mk-tuple-sort
  ; TODO mk-enumeration-sort
  [mk-list-sort : _z3-context _z3-symbol _z3-sort
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
                   tail-decl)]
  [mk-constructor :
    (ctx name recognizer names-sorts-refs) ::
    (ctx         : _z3-context)
    (name        : _z3-symbol)
    (recognizer  : _z3-symbol)
    (num-fields  : _uint = (length names-sorts-refs))
    (field-names : (_list i _z3-symbol) = (map car names-sorts-refs))
    (sorts       : (_list i _z3-sort/null) = (map cadr names-sorts-refs))
    (sort-refs   : (_list i _uint) = (map caddr names-sorts-refs))
    -> _z3-constructor]
  [del-constructor : _z3-context _z3-constructor -> _void]
  [mk-datatype :
    (ctx name constructors) ::
    (ctx : _z3-context)
    (name : _z3-symbol)
    (_uint = (length constructors))
    (constructors : (_list i _z3-constructor))
    -> _z3-sort]
  [mk-constructor-list : (ctx constructors) ::
    (ctx              : _z3-context)
    (num-constructors : _uint = (length constructors))
    (constructors     : (_list i _z3-constructor))
    -> _z3-constructor-list]
  [del-constructor-list : _z3-context _z3-constructor-list -> _void]
  [mk-datatypes : (ctx sort-decs) ::
    (ctx               : _z3-context)
    (num-sorts         : _uint = (length sort-decs))
    (sort-names        : (_list i _z3-symbol) = (map car sort-decs))
    (sorts             : (_list o _z3-sort num-sorts))
    (constructor-lists : (_list i _z3-constructor-list) = (map cdr sort-decs))
    -> _void
    -> sorts]
  [query-constructor :
    (ctx constructor num-fields) ::
    (ctx            : _z3-context)
    (constructor    : _z3-constructor)
    (num-fields     : _uint)
    (constructor-fn : (_ptr o _z3-func-decl))
    (tester-fn      : (_ptr o _z3-func-decl))
    (accessor-fns   : (_list o _z3-func-decl num-fields))
    -> _void ->
    (values constructor-fn tester-fn accessor-fns)]

  [mk-true : _z3-context -> _z3-ast]
  [mk-false : _z3-context -> _z3-ast]
  [mk-eq : _z3-context _z3-ast _z3-ast -> _z3-ast]

  (mk-distinct : _z3-context _z3-ast * -> _z3-ast)

  ;; Boolean operations
  [mk-not : _z3-context _z3-ast -> _z3-ast]
  [mk-ite : _z3-context _z3-ast _z3-ast _z3-ast -> _z3-ast]
  [mk-iff : _z3-context _z3-ast _z3-ast -> _z3-ast]
  [mk-implies : _z3-context _z3-ast _z3-ast -> _z3-ast]
  [mk-xor : _z3-context _z3-ast _z3-ast -> _z3-ast]
  [mk-and : _z3-context _z3-ast * -> _z3-ast]
  [mk-or : _z3-context _z3-ast * -> _z3-ast]

  ;; Arithmetic operations
  [mk-add : _z3-context _z3-ast * -> _z3-ast]
  [mk-mul : _z3-context _z3-ast * -> _z3-ast]
  [mk-sub : _z3-context _z3-ast * -> _z3-ast]
  [mk-div : _z3-context _z3-ast _z3-ast -> _z3-ast]
  [mk-mod : _z3-context _z3-ast _z3-ast -> _z3-ast]
  [mk-rem : _z3-context _z3-ast _z3-ast -> _z3-ast]
  [mk-power : _z3-context _z3-ast _z3-ast -> _z3-ast]
  [mk-is-int : _z3-context _z3-ast -> _z3-ast]
  [mk-int2real : _z3-context _z3-ast -> _z3-ast]

  ;; Comparisons
  [mk-lt : _z3-context _z3-ast _z3-ast -> _z3-ast]
  [mk-le : _z3-context _z3-ast _z3-ast -> _z3-ast]
  [mk-gt : _z3-context _z3-ast _z3-ast -> _z3-ast]
  [mk-ge : _z3-context _z3-ast _z3-ast -> _z3-ast]

  ;; Numerals
  [mk-numeral : _z3-context _string _z3-sort -> _z3-ast]

  ;; Constants and Applications
  [mk-func-decl : (ctx name dom rng) ::
    (ctx      : _z3-context)
    (name     : _z3-symbol)
    (dom-size : _uint = (length dom))
    (dom      : (_list i _z3-sort))
    (rng      : _z3-sort)
    -> _z3-func-decl]
  [mk-app : (ctx d . args) ::
    (ctx      : _z3-context)
    (d        : _z3-func-decl)
    (num-args : _uint = (length args))
    (args     : (_list i _z3-ast)) -> _z3-ast]
  [mk-const : _z3-context _z3-symbol _z3-sort -> _z3-app]
  [mk-fresh-func-decl : (ctx prefix dom rng) ::
    (ctx      : _z3-context)
    (prefix   : _string)
    (dom-size : _uint = (length dom))
    (dom      : (_list i _z3-sort))
    (rng      : _z3-sort)
    -> _z3-func-decl]
  [mk-fresh-const : _z3-context _string _z3-sort -> _z3-app]

  ;; Arrays
  [mk-select : _z3-context _z3-ast _z3-ast -> _z3-ast]
  [mk-store : _z3-context _z3-ast _z3-ast _z3-ast -> _z3-ast]
  [mk-const-array : _z3-context _z3-sort _z3-ast -> _z3-ast]
  [mk-map : (ctx f . args) ::
    (ctx      : _z3-context)
    (f        : _z3-func-decl)
    (num-args : _uint = (length args))
    (args     : (_list i _z3-ast))
    -> _z3-ast]
  [mk-array-default : _z3-context _z3-ast -> _z3-ast]

  ;; Sets
  [mk-set-sort : _z3-context _z3-sort -> _z3-sort]
  [mk-empty-set : _z3-context _z3-sort -> _z3-ast]
  [mk-full-set : _z3-context _z3-sort -> _z3-ast]
  [mk-set-add : _z3-context _z3-ast _z3-ast -> _z3-ast]
  [mk-set-del : _z3-context _z3-ast _z3-ast -> _z3-ast]
  [mk-set-union : _z3-context _z3-ast * -> _z3-ast]
  [mk-set-intersect : _z3-context _z3-ast * -> _z3-ast]
  [mk-set-difference : _z3-context _z3-ast _z3-ast -> _z3-ast]
  [mk-set-complement : _z3-context _z3-ast -> _z3-ast]
  [mk-set-member : _z3-context _z3-ast _z3-ast -> _z3-ast]
  [mk-set-subset : _z3-context _z3-ast _z3-ast -> _z3-ast]

  ;; Quantifiers
  [mk-pattern : (ctx t . ts) ::
    (ctx  : _z3-context)
    (num-patterns : _uint = (+ 1 (length ts)))
    (terms : (_list i _z3-ast) = (cons t ts))
    -> _z3-pattern]
  [mk-bound : _z3-context _uint _z3-sort -> _z3-ast]
  [mk-forall : (ctx weight patterns decls body) ::
    (ctx          : _z3-context)
    (weight       : _uint)
    (num-patterns : _uint = (length patterns))
    (patterns     : (_list i _z3-pattern))
    (num-decls    : _uint = (length decls))
    (decl-sorts   : (_list i _z3-sort  ) = (map cdr decls))
    (decl-names   : (_list i _z3-symbol) = (map car decls))
    (body         : _z3-ast)
    -> _z3-ast]
  [mk-exists : (ctx weight patterns decls body) ::
    (ctx          : _z3-context)
    (weight       : _uint)
    (num-patterns : _uint = (length patterns))
    (patterns     : (_list i _z3-pattern))
    (num-decls    : _uint = (length decls))
    (decl-sorts   : (_list i _z3-sort  ) = (map cdr decls))
    (decl-names   : (_list i _z3-symbol) = (map car decls))
    (body         : _z3-ast)
    -> _z3-ast]
  [mk-quantifier : (ctx forall? weight patterns decls body) ::
    (ctx : _z3-context)
    (forall? : _bool)
    (weight : _uint)
    (num-patterns : _uint = (length patterns))
    (patterns : (_list i _z3-pattern))
    (num-decls : _uint = (length decls))
    (decl-sorts : (_list i _z3-sort  ) = (map cdr decls))
    (decl-names : (_list i _z3-symbol) = (map car decls))
    (body : _z3-ast)
    -> _z3-ast]
  ;; TODO mk-quantifier-ex
  [mk-forall-const :
    (ctx weight bound-consts patterns body) ::
    (ctx          : _z3-context)
    (weight       : _uint)
    (num-bound    : _uint = (length bound-consts))
    (bound-consts : (_list i _z3-app))
    (num-patterns : _uint = (length patterns))
    (patterns     : (_list i _z3-pattern))
    (body         : _z3-ast)
    -> _z3-ast]
  [mk-exists-const :
    (ctx weight bound-consts patterns body) ::
    (ctx          : _z3-context)
    (weight       : _uint)
    (num-bound    : _uint = (length bound-consts))
    (bound-consts : (_list i _z3-app))
    (num-patterns : _uint = (length patterns))
    (patterns     : (_list i _z3-pattern))
    (body         : _z3-ast)
    -> _z3-ast]
  [mk-quantifier-const :
    (ctx forall? weight bound-consts patterns body) ::
    (ctx : _z3-context)
    (forall? : _bool)
    (weight       : _uint)
    (num-bound    : _uint = (length bound-consts))
    (bound-consts : (_list i _z3-app))
    (num-patterns : _uint = (length patterns))
    (patterns     : (_list i _z3-pattern))
    (body         : _z3-ast)
    -> _z3-ast]
  ; TODO mk-quantifier-const-ex

  ;; Accessors
  ; TODO many
  [get-symbol-string : _z3-context _z3-symbol -> _string]
  ; TODO many
  [get-decl-name : _z3-context _z3-func-decl -> _z3-symbol]
  ; TODO get-decl-kind
  [get-domain-size : _z3-context _z3-func-decl -> _uint]
  [get-arity : _z3-context _z3-func-decl -> _uint]
  [get-domain : _z3-context _z3-func-decl _uint -> _z3-sort]
  [get-range : _z3-context _z3-func-decl -> _z3-sort]
  ; TODO many
  [app->ast : _z3-context _z3-app -> _z3-ast]
  [get-app-decl : _z3-context _z3-app -> _z3-func-decl]
  [get-app-num-args : _z3-context _z3-app -> _uint]
  [get-app-arg : _z3-context _z3-app _uint -> _z3-ast]
  ; TODO many
  [get-sort : _z3-context _z3-ast -> _z3-sort]
  ; TODO many
  [get-bool-value : _z3-context _z3-ast -> _z3-lbool]
  [get-ast-kind : _z3-context _z3-ast -> _z3-ast-kind]
  ; TODO many
  [is-numeral-ast? : _z3-context _z3-ast -> _bool]
  ; TODO many
  [to-app : _z3-context _z3-ast -> _z3-app]
  ; TODO many
  [get-numeral-string : _z3-context _z3-ast -> _string]
  ; TODO many

  ;; String conversion
  [set-ast-print-mode! : _z3-context _z3-ast-print-mode -> _void]
  [ast->string : _z3-context _z3-ast -> _string]
  [pattern->string : _z3-context _z3-pattern -> _string]
  [sort->string : _z3-context _z3-sort -> _string]
  [func-decl->string : _z3-context _z3-func-decl -> _string]
  [model->string : _z3-context _z3-model -> _string]
  ; TODO benchmark->smtlib-string

  ;; Parser interface
  [parse-smtlib2-string : (ctx str sorts decls) ::
    (ctx : _z3-context)
    (str : _string)
    (num-sorts : _uint = (length sorts))
    (sort-names : (_list i _z3-symbol) = (map car sorts))
    (sort-vals  : (_list i _z3-sort) = (map cdr sorts))
    (num-decls  : _uint = (length decls))
    (decl-names : (_list i _z3-symbol) = (map car decls))
    (decl-vals  : (_list i _z3-func-decl) = (map cdr decls))
    -> _z3-ast]
  [parse-smtlib2-file : (ctx fn sorts decls) ::
    (ctx : _z3-context)
    (fn  : _string)
    (num-sorts : _uint = (length sorts))
    (sort-names : (_list i _z3-symbol) = (map car sorts))
    (sort-vals  : (_list i _z3-sort) = (map cdr sorts))
    (num-decls  : _uint = (length decls))
    (decl-names : (_list i _z3-symbol) = (map car decls))
    (decl-vals  : (_list i _z3-func-decl) = (map cdr decls))
    -> _z3-ast]
  [parse-smtlib-string! : (ctx str sorts decls) ::
    (ctx : _z3-context)
    (str : _string)
    (num-sorts : _uint = (length sorts))
    (sort-names : (_list i _z3-symbol) = (map car sorts))
    (sort-vals  : (_list i _z3-sort) = (map cdr sorts))
    (num-decls  : _uint = (length decls))
    (decl-names : (_list i _z3-symbol) = (map car decls))
    (decl-vals  : (_list i _z3-func-decl) = (map cdr decls))
    -> _void]
  [parse-smtlib-file! : (ctx fn sorts decls) ::
    (ctx : _z3-context)
    (fn  : _string)
    (num-sorts : _uint = (length sorts))
    (sort-names : (_list i _z3-symbol) = (map car sorts))
    (sort-vals  : (_list i _z3-sort) = (map cdr sorts))
    (num-decls  : _uint = (length decls))
    (decl-names : (_list i _z3-symbol) = (map car decls))
    (decl-vals  : (_list i _z3-func-decl) = (map cdr decls))
    -> _void]
  [get-smtlib-num-formulas : _z3-context -> _uint]
  [get-smtlib-formula : _z3-context _uint -> _z3-ast]
  [get-smtlib-num-assumptions : _z3-context -> _uint]
  [get-smtlib-assumption : _z3-context _uint -> _z3-ast]
  [get-smtlib-num-decls : _z3-context -> _uint]
  [get-smtlib-decl : _z3-context _uint -> _z3-func-decl]
  [get-smtlib-num-sorts : _z3-context -> _uint]
  [get-smtlib-sort : _z3-context _uint -> _z3-sort]
  [get-smtlib-error : _z3-context -> _string]

  ;; Error Handling
  [get-error-code : _z3-context -> _z3-error-code]
  ;[set-error-handler! : _z3-context (_fun _z3-context _z3-error-code -> _void) -> _void] ; FIXME not working
  [get-error-msg : _z3-error-code -> _string]

  ;; Model
  [model-inc-ref! : _z3-context _z3-model -> _void]
  [model-dec-ref! : _z3-context _z3-model -> _void]
  [model-eval : _z3-context _z3-model _z3-ast _bool (res : (_ptr o _z3-ast))
    -> (ok? : _bool)
    -> (and ok? res)]
  [model-get-const-interp : _z3-context _z3-model _z3-func-decl -> _z3-ast]
  [model-has-interp? : _z3-context _z3-model _z3-func-decl -> _bool]
  [model-get-func-interp : _z3-context _z3-model _z3-func-decl -> _z3-func-interp/null]
  [model-get-num-consts : _z3-context _z3-model -> _uint]
  [model-get-const-decl : _z3-context _z3-model _uint -> _z3-func-decl]
  [model-get-num-funcs : _z3-context _z3-model -> _uint]
  [model-get-func-decl : _z3-context _z3-model _uint -> _z3-func-decl]
  [model-get-num-sorts : _z3-context _z3-model -> _uint]
  [model-get-sort : _z3-context _z3-model _uint -> _z3-sort]
  [model-get-sort-universe : _z3-context _z3-model _z3-sort -> _z3-ast-vector]
  [is-as-array? : _z3-context _z3-ast -> _bool]
  [get-as-array-func-decl : _z3-context _z3-ast -> _z3-func-decl]
  [func-interp-inc-ref! : _z3-context _z3-func-interp -> _void]
  [func-interp-dec-ref! : _z3-context _z3-func-interp -> _void]
  [func-interp-get-num-entries : _z3-context _z3-func-interp -> _uint]
  [func-interp-get-entry : _z3-context _z3-func-interp _uint -> _z3-func-entry]
  [func-interp-get-else : _z3-context _z3-func-interp -> _z3-ast]
  [func-interp-get-arity : _z3-context _z3-func-interp -> _uint]
  [func-entry-inc-ref! : _z3-context _z3-func-entry -> _void]
  [func-entry-dec-ref! : _z3-context _z3-func-entry -> _void]
  [func-entry-get-value : _z3-context _z3-func-entry -> _z3-ast]
  [func-entry-get-num-args : _z3-context _z3-func-entry -> _uint]
  [func-entry-get-arg : _z3-context _z3-func-entry _uint -> _z3-ast]

  ;; Interaction logging
  [open-log : _string -> _bool]
  [append-log! : _string -> _void]
  [close-log! : -> _bool]
  [toggle-warning-messages! : _bool -> _void]

  ;; Statistics
  [stats->string : _z3-context _z3-stats -> _string]
  [stats-inc-ref! : _z3-context _z3-stats -> _void]
  [stats-dec-ref! : _z3-context _z3-stats -> _void]
  [stats-size : _z3-context _z3-stats -> _uint]
  [stats-get-key : _z3-context _z3-stats _uint -> _string]
  [stats-is-uint? : _z3-context _z3-stats _uint -> _bool]
  [stats-is-double? : _z3-context _z3-stats _uint -> _bool]
  [stats-get-uint-value : _z3-context _z3-stats _uint -> _uint]
  [stats-get-double-value : _z3-context _z3-stats _uint -> _double]

  ;; AST Vectors
  [mk-ast-vector : _z3-context -> _z3-ast-vector]
  [ast-vector-inc-ref! : _z3-context _z3-ast-vector -> _void]
  [ast-vector-dec-ref! : _z3-context _z3-ast-vector -> _void]
  [ast-vector-size : _z3-context _z3-ast-vector -> _uint]
  [ast-vector-get : _z3-context _z3-ast-vector _uint -> _z3-ast]
  [ast-vector-set! : _z3-context _z3-ast-vector _uint _z3-ast -> _void]
  [ast-vector-resize! : _z3-context _z3-ast-vector _uint -> _void]
  [ast-vector-push! : _z3-context _z3-ast-vector _z3-ast -> _void]
  [ast-vector-translate : _z3-context _z3-ast-vector _z3-context -> _z3-ast-vector]
  [ast-vector->string : _z3-context _z3-ast-vector -> _string]

  ;; Miscellaneous
  [get-version :
    (major           : (_ptr o _uint))
    (minor           : (_ptr o _uint))
    (build-number    : (_ptr o _uint))
    (revision-number : (_ptr o _uint))
    -> _void
    -> (values major minor build-number revision-number)]
  [enable-trace! : _string -> _void]
  [disable-trace! : _string -> _void]
  [reset-memory! : -> _void]
  [finalize-memory! : -> _void]
  )
