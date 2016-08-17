#lang typed/racket/base

(provide (all-defined-out))

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         racket/match
         syntax/parse/define)

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

(require/typed/provide "z3-wrapper-untyped.rkt"
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
(define-type Sort-Expr (U Z3:Sort Symbol))

(require/typed/provide "z3-wrapper-untyped.rkt"
  [toggle-warning-messages! (Boolean → Void)]
  [global-param-set! (Global-Param String → Void)]
  [global-param-get (Global-Param → String)]
  
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Enhanced interface for low-level functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require/typed racket/base
  [(make-keyword-procedure
    make-config-keyword-procedure)
   (((Listof Keyword) (Listof (U Boolean Integer String)) → Z3:Config) →
    ([]
     [#:proof? Boolean
      #:debug-ref-count? Boolean
      #:trace? Boolean
      #:trace-file-name String
      #:timeout Nonnegative-Fixnum
      #:rlimit Nonnegative-Fixnum
      #:type-check? Boolean
      #:well-sorted-check? Boolean
      #:auto-config? Boolean
      #:model? Boolean
      #:model-validate? Boolean
      #:unsat-core? Boolean]
     . ->* . Z3:Config))])

(require/typed "z3-wrapper-untyped.rkt"
  [(mk-config raw:mk-config) (→ Z3:Config)])

(define mk-config
  (let ()

    (: keyword-arg->_z3-param : Keyword (U Boolean Integer String) → (Values String String))
    (define (keyword-arg->_z3-param kw kw-arg)
      (define kw-str (assert (regexp-replaces (keyword->string kw)
                                              '((#rx"-" "_") (#rx"\\?$" "")))
                             string?))
      (define kw-arg-str (match kw-arg
                           [#t "true"]
                           [#f "false"]
                           [(? integer?) (number->string kw-arg)]
                           [(? string?) kw-arg]))
      (values kw-str kw-arg-str))

    (make-config-keyword-procedure
     (λ (kws kw-args)
       (define cfg (raw:mk-config))
       (for ([kw kws] [kw-arg kw-args])
         (define-values (k v) (keyword-arg->_z3-param kw kw-arg))
         (set-param-value! cfg k v))
       cfg))))

;; Given an expr, convert it to a Z3 AST. This is a really simple recursive descent parser.
;; PN: This no longer is a parser. It only coerces some base values now
(: expr->_z3-ast : Expr → Z3:Ast)
(define (expr->_z3-ast e)
  ;(displayln (format "IN: ~a" e))
  (define cur-ctx (get-context))
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

(: sort-expr->_z3-sort : Sort-Expr → (U Z3:Sort Z3:Null))
;; sort-exprs are sort ids, (_ id parameter*), or (id sort-expr*).
;; PN: Only have simple sorts for now, which makes it just simple lookup
(define (sort-expr->_z3-sort expr)
  (match expr
    [(? symbol? id)
     (define s (get-sort id))
     (if (z3-sort? s) s z3-null)]
    [(? z3-sort? expr) expr]
    [_ (error 'sort-expr->_z3-sort "unexpected: ~a" expr)]))

(: mk-func : Z3:Func-Decl Symbol Natural → Z3:Func)
;; Make a 1st order Z3 function out of func-decl
(define (mk-func f-decl name n)
  (λ xs
    (define num-xs (length xs))
    (cond [(= n num-xs)
           (define cur-ctx (get-context))
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

(struct Env ([vals : (HashTable Symbol Z3:Ast)]
             [funs : (HashTable Symbol Z3:Func)]
             [sorts : (HashTable Symbol Z3:Sort)])
  #:transparent
  #:mutable)

(define-syntax (define-z3-context-parameter stx)
  (syntax-parse stx
    [(_ param:id (~literal :) T)
     (with-syntax (;[current-param (format-id stx "current-~a" #'param)] hide direct access
                   [get-param     (format-id stx     "get-~a" #'param)]
                   [with-param    (format-id stx "   with-~a" #'param)])
       #'(begin
           (define current-param : (Parameterof (Option T)) (make-parameter #f))
           (define (get-param) : T
             (cond
               [(current-param) => values]
               [else (error 'get-param "Expect ~a to have been parameterized through ~a"
                            'param
                            'with-param)]))
           (define-syntax-rule (with-param t e (... ...))
             (parameterize ([current-param t]) e (... ...)))))]))

(define-z3-context-parameter context : Z3:Context)
(define-z3-context-parameter solver  : Z3:Solver)
(define-z3-context-parameter env     : Env)

;; A symbol table for sorts
(: get-sort : Symbol → (Option Z3:Sort))
(define (get-sort id)
  (hash-ref (Env-sorts (get-env)) id #f))

(: new-sort! : Symbol Z3:Sort → Void)
(define (new-sort! id v)
  (define env (get-env))
  (define sorts (Env-sorts env))
  (cond [(hash-has-key? sorts id)
         (error 'new-sort! "Defining a pre-existing sort: ~a" id)]
        [else
         (set-Env-sorts! env (hash-set sorts id v))]))

(: set-val! : Symbol Z3:Ast → Void)
(define (set-val! id v)
  (define env (get-env))
  (define vals (Env-vals env))
  (set-Env-vals! env (hash-set vals id v)))

(: get-val : Symbol → Z3:Ast)
(define (get-val id)
  (define vals (Env-vals (get-env)))
  (hash-ref vals id (λ ()
                      (error 'get-val "cannot find `~a` among ~a" id (hash-keys vals)))))

(: set-fun! : Symbol Z3:Func → Void)
(define (set-fun! id v)
  (define env (get-env))
  (define funs (Env-funs env))
  (set-Env-funs! env (hash-set funs id v)))

(: get-fun : Symbol → Z3:Func)
(define (get-fun id)
  (define funs (Env-funs (get-env)))
  (hash-ref funs id (λ ()
                      (error 'get-fun "cannot find `~a` among ~a" id (hash-keys funs)))))

;; Primitive sorts
(define (Int/s) (get-sort 'Int))
(define (Real/s) (get-sort 'Real))
(define (Bool/s) (get-sort 'Bool))

;; Primitive constants
(define (true/s) (get-val 'true))
(define (false/s) (get-val 'false))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Bookeeping forms
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Run expression, parameterizing with fresh context, which is discarded at the end
(define-syntax-rule (with-fresh-context (args ...) e ...)
  (let ()
    (define cfg (mk-config args ...))
    (define ctx (mk-context cfg))
    (define solver (mk-solver ctx))
    (solver-inc-ref! solver)
    (begin0
        (with-context ctx
          (with-solver solver
            e ...))
      (solver-dec-ref! solver)
      (del-context ctx)
      (del-config cfg))))

(define-syntax-rule (with-init-env e ...) (with-env (init-env) e ...))

(define-syntax-rule (with-vals x->v e ...)
  (match-let ([(Env vals funs sorts) (get-env)])
    (define vals*
      (for/fold ([vals* : (HashTable Symbol Z3:Ast) vals])
                ([(x v) x->v])
        (hash-set vals* x v)))
    (with-env (Env vals* funs sorts*) e ...)))

(define (init-env) : Env
  (define ctx (get-context))
  (define vals : (HashTable Symbol Z3:Ast)
    (hasheq 'true (mk-true ctx)
            'false (mk-false ctx)))
  (define funs : (HashTable Symbol Z3:Func)
    (hasheq))
  (define sorts : (HashTable Symbol Z3:Sort)
    (hasheq 'Int (mk-int-sort ctx)
            'Real (mk-real-sort ctx)
            'Bool (mk-bool-sort ctx)))
  (Env vals funs sorts))
