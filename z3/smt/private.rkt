#lang typed/racket/base

;; This module defines Z3 run-time context and parameters
(provide (except-out (all-defined-out)
                     (struct-out Env)))

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         racket/match
         racket/string
         racket/splicing
         "../ffi/main.rkt")

(define-type Smt-Expr (U Z3-Ast Z3-App Real Symbol))
(define-type Smt-Func (Smt-Expr * → Z3-Ast))
(define-type Smt-Sort-Expr (U Z3-Sort Symbol))
(define-type Smt-Sort-Func (Smt-Sort-Expr * → Z3-Sort))
(define-type Smt-Sat (U 'sat 'unsat 'unknown))

(struct Env ([vals  : (HashTable Symbol Z3-Ast)]
             [funs  : (HashTable Symbol Smt-Func)]
             [sorts : (HashTable Symbol Z3-Sort)]
             [sort-funs : (HashTable Symbol Smt-Sort-Func)])
  #:mutable
  #:transparent)

(splicing-local
    ((define-syntax (define-z3-parameter stx)
       (syntax-parse stx
         [(_ param:id (~literal :) T)
          (with-syntax ([get-param  (format-id stx "raw:get-~a" (syntax-e #'param))]
                        [with-param (format-id stx "with-~a" (syntax-e #'param))])
            #'(begin
                (define param : (Parameterof (Option T)) (make-parameter #f))
                (define (get-param) : T
                  (cond [(param) => values]
                        [else (error 'param "parameter not set")]))
                (define-syntax-rule (with-param x e (... ...))
                  (parameterize ([param x]) e (... ...)))))]))
     )
  
  (define-z3-parameter context : Z3-Context)
  (define-z3-parameter solver  : Z3-Solver)
  (define-z3-parameter env     : Env)
  
  (define get-context raw:get-context)
  (define get-solver  raw:get-solver)
  (define get-env     raw:get-env)
  
  ;; Initializing environment does not require resetting anything else
  (define-syntax-rule (with-new-environment e ...)
    (with-env (init-env (get-context))
      e ...))

  ;; Initializing solver does not require resetting anything else
  (define-syntax-rule (with-new-solver e ...)
    (let* ([ctx (get-context)]
           [solver (mk-solver ctx)])
      (solver-inc-ref! ctx solver)
      (begin0 (with-solver solver e ...)
        (solver-dec-ref! ctx solver))))

  ;; Initializing a context requires resetting solver and environments
  (define-syntax-rule (with-new-context e ...)
    (let ()
      (define cfg (mk-config))
      (define ctx (mk-context cfg))
      ;(printf "~n")
      (begin0 (with-context ctx
                (with-new-solver
                  (with-new-environment
                    e ...)))
        ;(printf "~n")
        (del-context! ctx)
        (del-config! cfg))))

  (define-syntax-rule (init-global-context!)
    (let* ([ctx (mk-context (mk-config))]
           [slvr (mk-solver ctx)]
           [nv (init-env ctx)])
      (solver-inc-ref! ctx slvr)
      (context ctx)
      (solver slvr)
      (env nv)))

  (define-syntax-rule (destroy-global-context!)
    (let ([ctx (get-context)]) ; TODO: no del-config ...
      (solver-dec-ref! ctx (get-solver))
      (del-context! ctx)
      (context #f)
      (solver #f)
      (env #f)))

  (define-syntax-rule (with-extended-vals new-vals e ...)
    (match-let ([(Env vals funs sorts sort-funs) (get-env)])
      (define vals*
        (for/fold ([acc : (HashTable Symbol Z3-Ast) vals])
                  ([(k v) new-vals])
          (hash-set acc k v)))
      (with-env (Env vals* funs sorts sort-funs)
        e ...))))

;; A symbol table for sorts
(: sort-of : Symbol → Z3-Sort)
(define (sort-of id)
  (define sorts (Env-sorts (get-env)))
  (hash-ref sorts id
            (λ ()
              (error 'sort-of "cannot find `~a` among ~a" id (hash-keys sorts)))))

(: new-sort! : Symbol Z3-Sort → Void)
(define (new-sort! id v)
  (define env (get-env))
  (define sorts (Env-sorts env))
  (cond [(hash-has-key? sorts id)
         (error 'new-sort! "Defining a pre-existing sort: ~a" id)]
        [else
         (set-Env-sorts! env (hash-set sorts id v))]))

(: set-val! : Symbol Z3-Ast → Void)
(define (set-val! id v)
  (define env (get-env))
  (define vals (Env-vals env))
  (set-Env-vals! env (hash-set vals id v)))

(: val-of : Symbol → Z3-Ast)
(define (val-of id)
  (define vals (Env-vals (get-env)))
  (hash-ref vals id (λ ()
                      (error 'val-of "cannot find `~a` among ~a" id (hash-keys vals)))))

(: set-fun! : Symbol Smt-Func → Void)
(define (set-fun! id v)
  (define env (get-env))
  (define funs (Env-funs env))
  (set-Env-funs! env (hash-set funs id v)))

(: fun-of : Symbol → Smt-Func)
(define (fun-of id)
  (define funs (Env-funs (get-env)))
  (hash-ref funs id (λ ()
                      (error 'fun-of "cannot find `~a` among ~a" id (hash-keys funs)))))

(: sort-of-fun : Symbol → Smt-Sort-Func)
(define (sort-of-fun id)
  (define sort-funs (Env-sort-funs (get-env)))
  (hash-ref sort-funs id (λ ()
                           (error 'sort-of-fun "cannot find `~a` among ~a" id (hash-keys sort-funs)))))

(: set-sort-fun! : Symbol Smt-Sort-Func → Void)
(define (set-sort-fun! id v)
  (define env (get-env))
  (define sort-funs (Env-sort-funs env))
  (set-Env-sort-funs! env (hash-set sort-funs id v)))

(: init-env : Z3-Context → Env)
(define (init-env ctx)
  (Env (hasheq) (hasheq) (hasheq) (hasheq)))

(: reset! : → Void)
(define (reset!)
  (define ctx (get-context))
  (define env (get-env))
  (set-Env-vals!      env (hasheq))
  (set-Env-funs!      env (hasheq))
  (set-Env-sorts!     env (hasheq))
  (set-Env-sort-funs! env (hasheq))
  (solver-reset! ctx (get-solver)))

(define-syntax-rule (with-local-stack e ...)
  (match-let ([ctx (get-context)]
              [solver (get-solver)]
              [(Env vals funs sorts sort-funs) (get-env)])
    (begin0
        (let ()
          (solver-push! ctx solver)
          (with-env (Env vals funs sorts sort-funs) ; copied environment
            e ...))
      (solver-pop! ctx solver 1))))

;; Given an expr, convert it to a Z3 AST. This is a really simple recursive descent parser.
;; PN: This no longer is a parser. It only coerces some base values now
(: expr->_z3-ast : Smt-Expr → Z3-Ast)
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
        [(? symbol? x) (val-of x)]
        ; Anything else
        [(? z3-app? e) (app->ast cur-ctx e)]
        [(? z3-ast? e) e]
        [_ (error 'expr->_z3-ast "unexpected: ~a" e)])))
  ;(displayln (format "Output: ~a ~a ~a" expr ast (z3:ast->string cur-ctx ast)))
  ast)

(: sort-expr->_z3-sort : Smt-Sort-Expr → Z3-Sort)
;; sort-exprs are sort ids, (_ id parameter*), or (id sort-expr*).
;; PN: Only have simple sorts for now, which makes it just simple lookup
(define (sort-expr->_z3-sort expr)
  (match expr
    [(? symbol? id) (sort-of id)]
    [(? z3-sort? expr) expr]
    [_ (error 'sort-expr->_z3-sort "unexpected: ~a" expr)]))

(: mk-func : Z3-Func-Decl Symbol Natural → Smt-Func)
;; Make a 1st order Z3 function out of func-decl
(define (mk-func f-decl name n)
  (λ xs
    (define num-xs (length xs))
    (cond [(= n num-xs)
           (define ctx (get-context))
           (define args (map expr->_z3-ast xs))
           #;(printf "applying ~a to ~a~n"
                     (func-decl->string ctx f-decl)
                     (for/list : (Listof Sexp) ([arg args])
                       (define arg-str (ast->string ctx arg))
                       (define sort (sort->string ctx (z3-sort-of ctx arg)))
                       `(,arg-str : ,sort)))
           (mk-app ctx f-decl args)]
          [else
           (error name "expect ~a arguments, given ~a: ~a"
                  n
                  num-xs
                  (string-join
                   (for/list : (Listof String) ([x xs])
                     (ast->string (get-context) (expr->_z3-ast x)))))])))

(: make-symbol : (U Symbol String) → Z3-Symbol)
;; Helper function to make a symbol with the given name (Racket symbol)
(define (make-symbol s)
  (cond [(string? s) (mk-string-symbol (get-context) s)]
        [else        (make-symbol (format "~a" s))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Hack for set-options!
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-type Param-Range (U Boolean Nonnegative-Fixnum Flonum Symbol))
(require/typed racket/base
  [(make-keyword-procedure
    make-set-options-procedure)
   (((Listof Keyword) (Listof Param-Range) → Void) →
    ([] ; type generated from `get-solver-param-descrs`
     [#:resolution.cls-cutoff1 Nonnegative-Fixnum
      #:asymm-branch.limit Nonnegative-Fixnum
      #:sort-store? Boolean
      #:gc.small-lbd Nonnegative-Fixnum
      #:theory-solver? Boolean
      #:common-patterns? Boolean
      #:expand-store-eq? Boolean
      #:elim-inverses? Boolean
      #:gc.increment Nonnegative-Fixnum
      #:extrapolate-strategy Nonnegative-Fixnum
      #:ematching? Boolean
      #:ite-chaing? Boolean
      #:blast-distinct-threshold Nonnegative-Fixnum
      #:mode Symbol
      #:ignore-solver1? Boolean
      #:mbqi.max-cexs Nonnegative-Fixnum
      #:timeout Nonnegative-Fixnum
      #:add-bound-upper Nonnegative-Fixnum ; TODO "other"
      #:hoist-cmul? Boolean
      #:phase-selection Nonnegative-Fixnum
      #:dimacs.core? Boolean
      #:elim-vars? Boolean
      #:array.weak? Boolean
      #:cofactor-equalities? Boolean
      #:array.extensional? Boolean
      #:factor-max-prime Nonnegative-Fixnum
      #:strong-context-simplify-local? Boolean
      #:qe-nonlinear? Boolean
      #:mul2concat? Boolean
      #:max-steps Nonnegative-Fixnum
      #:random-freq Flonum
      #:candidate-models? Boolean
      #:phase.caching.on Nonnegative-Fixnum
      #:max-args Nonnegative-Fixnum
      #:elim-rem? Boolean
      #:elim-root-objects? Boolean
      #:dack.eq? Boolean
      #:factor? Boolean
      #:pull-nested-quantifiers? Boolean
      #:blast-add? Boolean
      #:pull-cheap-ite? Boolean
      #:pb.enable-compilation? Boolean
      #:gc.initial Nonnegative-Fixnum
      #:arith.propagation-mode Nonnegative-Fixnum
      #:dack.gc Nonnegative-Fixnum
      #:hi-div0? Boolean
      #:lia2pb-total-bits Nonnegative-Fixnum
      #:blast-distinct? Boolean
      #:bv.reflect? Boolean
      #:resolution.occ-cutoff Nonnegative-Fixnum
      #:dack.factor Flonum
      #:split-concat-eq? Boolean
      #:reorder? Boolean
      #:mbqi.id Symbol ; TODO: "string"
      #:min-mag Nonnegative-Fixnum
      #:aig-per-assertion? Boolean
      #:arith.nl.branching? Boolean
      #:blocked-clause-limit Nonnegative-Fixnum
      #:delay-units? Boolean
      #:arith.dump-lemmas? Boolean
      #:minimize-core? Boolean
      #:skolemize? Boolean
      #:minimize-core-partial? Boolean
      #:case-split Nonnegative-Fixnum
      #:resolution.occ-cutoff-range2 Nonnegative-Fixnum
      #:lia2pb-partial? Boolean
      #:arith.euclidean-solver? Boolean
      #:resolution.occ-cutoff-range3 Nonnegative-Fixnum
      #:solver2-timeout Nonnegative-Fixnum
      #:mul-to-power? Boolean
      #:rlimit Nonnegative-Fixnum
      #:pb2bv-all-clauses-limit Nonnegative-Fixnum
      #:minimize-conflicts? Boolean
      #:random-seed Nonnegative-Fixnum
      #:solver2-unknown Nonnegative-Fixnum
      #:asymm-branch? Boolean
      #:ite-solver? Boolean
      #:resolution.lit-cutoff-range2 Nonnegative-Fixnum
      #:hoist-mul? Boolean
      #:nla2bv-max-bv-size Nonnegative-Fixnum
      #:nla2bv-divisor Nonnegative-Fixnum
      #:dack Nonnegative-Fixnum
      #:mbqi? Boolean
      #:arith.nl.rounds Nonnegative-Fixnum
      #:flat? Boolean
      #:max-search-size Nonnegative-Fixnum
      #:restart.initial Nonnegative-Fixnum
      #:resolution.lit-cutoff-range3 Nonnegative-Fixnum
      #:bit2Boolean? Boolean
      #:asymm-branch.rounds Nonnegative-Fixnum
      #:resolution.cls-cutoff2 Nonnegative-Fixnum
      #:elim-blocked-clauses? Boolean
      #:phase Symbol
      #:mbqi.force-template Nonnegative-Fixnum
      #:minimize-lemmas? Boolean
      #:dyn-sub-res? Boolean
      #:zero-accuracy Nonnegative-Fixnum
      #:dack.threshold Nonnegative-Fixnum
      #:resolution.limit Nonnegative-Fixnum
      #:split-factors? Boolean
      #:projection-mode? Boolean
      #:resolution.lit-cutoff-range1 Nonnegative-Fixnum
      #:subsumption? Boolean
      #:norm-int-only? Boolean
      #:lia2pb-max-bits Nonnegative-Fixnum
      #:expand-power? Boolean
      #:elim-sign-ext? Boolean
      #:optimize-model? Boolean
      #:elim-to-real? Boolean
      #:som-blowup Nonnegative-Fixnum
      #:sort-sums? Boolean
      #:bvnot2arith? Boolean
      #:qi.lazy-threshold Flonum
      #:proof? Boolean
      #:max-prime Nonnegative-Fixnum
      #:qi.max-multi-patterns Nonnegative-Fixnum
      #:blast-eq-value? Boolean
      #:macro-finder? Boolean
      #:arith-lhs? Boolean
      #:blast-quant? Boolean
      #:local-ctx-limit Nonnegative-Fixnum
      #:fail-if-inconclusive? Boolean
      #:elim-and? Boolean
      #:mbqi.trace? Boolean
      #:scc? Boolean
      #:elim-blocked-clauses-at Nonnegative-Fixnum
      #:gcd-rounding? Boolean
      #:seed Nonnegative-Fixnum
      #:strong-context-simplify? Boolean
      #:bv.enable-int2bv? Boolean
      #:eliminate-variables-as-block? Boolean
      #:ite-extra-rules? Boolean
      #:arith.ignore-int? Boolean
      #:eq2ineq? Boolean
      #:qi.profile? Boolean
      #:refine-inj-axioms? Boolean
      #:max-depth Nonnegative-Fixnum
      #:nla2bv-bv-size Nonnegative-Fixnum
      #:model? Boolean
      #:solve-eqs-max-occs Nonnegative-Fixnum
      #:restart-factor Flonum
      #:auto-config? Boolean
      #:phase.caching.off Nonnegative-Fixnum
      #:restart Symbol
      #:expand-tan? Boolean
      #:qi.profile-freq Nonnegative-Fixnum
      #:unsat-core? Boolean
      #:pb.learn-complements? Boolean
      #:pb.enable-simplex? Boolean
      #:resolution? Boolean
      #:sk-hack? Boolean
      #:arith.branch-cut-ratio Nonnegative-Fixnum
      #:factor-num-primes Nonnegative-Fixnum
      #:expand-select-store? Boolean
      #:arith.nl? Boolean
      #:restart.factor Flonum
      #:complete? Boolean
      #:max-memory Nonnegative-Fixnum
      #:blast-mul? Boolean
      #:resolution.occ-cutoff-range1 Nonnegative-Fixnum
      #:simplify-conflicts? Boolean
      #:bv-sort-ac? Boolean
      #:factor-search-size Nonnegative-Fixnum
      #:qi.cost Symbol ; TODO: "string"
      #:add-bound-lower Nonnegative-Fixnum ; TODO "other"
      #:randomize? Boolean
      #:bcd? Boolean
      #:subsumption.limit Nonnegative-Fixnum
      #:burst-search Nonnegative-Fixnum
      #:algebraic-number-evaluator? Boolean
      #:qi.eager-threshold Flonum
      #:blast-full? Boolean
      #:lazy Nonnegative-Fixnum
      #:arith.int-eq-branch? Boolean
      #:relevancy Nonnegative-Fixnum
      #:restart-strategy Nonnegative-Fixnum
      #:arith.propagate-eqs? Boolean
      #:push-ite-arith? Boolean
      #:arith.greatest-error-pivot? Boolean
      #:shuffle-vars? Boolean
      #:dack.gc-inv-decay Flonum
      #:qi.max-instances Nonnegative-Fixnum
      #:mbqi.max-cexs-incr Nonnegative-Fixnum
      #:push-to-real? Boolean
      #:max-conflicts Nonnegative-Fixnum
      #:produce-models? Boolean
      #:arith.solver Nonnegative-Fixnum
      #:arith.random-initial-value? Boolean
      #:som? Boolean
      #:ignore-labels? Boolean
      #:gc.k Nonnegative-Fixnum
      #:delay-units-threshold Nonnegative-Fixnum
      #:max-degree Nonnegative-Fixnum
      #:pb.conflict-frequency Nonnegative-Fixnum
      #:push-ite-bv? Boolean
      #:num-primes Nonnegative-Fixnum
      #:cache-all? Boolean
      #:core.validate? Boolean
      #:max-rounds Nonnegative-Fixnum
      #:mbqi.max-iterations Nonnegative-Fixnum
      #:gc Symbol
      #:ite-extra? Boolean
      #:distributivity? Boolean
      #:learned? Boolean
      #:nla2bv-root Nonnegative-Fixnum
      #:local-ctx? Boolean
      #:distributivity-blowup Nonnegative-Fixnum
      #:pb2bv-cardinality-limit Nonnegative-Fixnum
      #:arith.nl.gb? Boolean
      #:udiv2mul? Boolean]
     . ->* . Void))])

(define set-options!
  (let ()
    
    (: raw:set-options! : (Listof Keyword) (Listof Param-Range) → Void)
    (define (raw:set-options! kws args)
      (unless (null? kws)
        (define c (get-context))
        (define prms (mk-params c))
        (params-inc-ref! c prms)
        (for ([kw kws] [v args])
          (define k (assert (regexp-replaces (keyword->string kw) '((#rx"-" "_") (#rx"\\?$" ""))) string?))
          (define k-sym (make-symbol k))
          (cond [(boolean? v)      (params-set-bool!   c prms k-sym v)]
                [(fixnum? v)       (params-set-uint!   c prms k-sym v)]
                [(flonum? v)       (params-set-double! c prms k-sym v)]
                [else              (params-set-symbol! c prms k-sym (make-symbol v))]))
        (solver-set-params! c (get-solver) prms)
        (params-dec-ref! c prms)))
    
    (make-set-options-procedure raw:set-options!)))
