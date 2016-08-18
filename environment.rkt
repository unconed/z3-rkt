#lang typed/racket/base

;; This module defines Z3 run-time context and parameters
(provide (except-out (all-defined-out)
                     (struct-out Env)))

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         racket/match
         racket/splicing
         "z3-wrapper.rkt")


(struct Env ([vals  : (HashTable Symbol Z3:Ast)]
             [funs  : (HashTable Symbol Z3:Func)]
             [sorts : (HashTable Symbol Z3:Sort)])
  #:mutable
  #:transparent)

(splicing-local
    ((define-syntax (define-z3-parameter stx)
       (syntax-parse stx
         [(_ param:id (~literal :) T)
          (with-syntax ([get-param  (format-id stx "get-~a" (syntax-e #'param))]
                        [with-param (format-id stx "with-~a" (syntax-e #'param))])
            #'(begin
                (define current-param : (Parameterof (Option T)) (make-parameter #f))
                (define (get-param) : T
                  (cond [(current-param) => values]
                        [else (error 'param "parameter not set")]))
                (define-syntax-rule (with-param x e (... ...))
                  (parameterize ([current-param x]) e (... ...)))))]))
     (define-z3-parameter context : Z3:Context)
     (define-z3-parameter solver  : Z3:Solver)
     (define-z3-parameter env     : Env))
  
  (define get-context get-context)
  (define get-solver  get-solver)
  (define get-env     get-env)
  
  ;; Initializing environment does not require resetting anything else
  (define-syntax-rule (with-fresh-environment e ...)
    (with-env (init-env (get-context))
      e ...))

  ;; Initializing solver does not require resetting anything else
  (define-syntax-rule (with-fresh-solver e ...)
    (let* ([ctx (get-context)]
           [solver (mk-solver ctx)])
      (solver-inc-ref! ctx solver)
      (begin0 (with-solver solver e ...)
        (solver-dec-ref! ctx solver))))

  ;; Initializing a context requires resetting solver and environments
  (define-syntax-rule (with-fresh-context (config-args ...) e ...)
    (let ()
      (define cfg (mk-config config-args ...))
      (define ctx (mk-context cfg))
      (begin0 (with-context ctx
                (with-fresh-solver
                  (with-fresh-environment
                    e ...)))
        (del-context ctx)
        (del-config cfg))))

  (define-syntax-rule (with-extended-vals new-vals e ...)
    (let* ([env (get-env)]
           [vals*
            (for/fold ([acc : (HashTable Symbol Z3:Ast) (Env-vals env)])
                      ([(k v) new-vals])
              (hash-set acc k v))])
      (with-env (Env vals* (Env-funs env) (Env-sorts env))
        e ...))))

;; A symbol table for sorts
(: get-sort : Symbol → Z3:Sort)
(define (get-sort id)
  (define sorts (Env-sorts (get-env)))
  (hash-ref sorts id
            (λ ()
              (error 'get-sort "cannot find `~a` among ~a" id (hash-keys sorts)))))

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

(: init-vals : Z3:Context → (HashTable Symbol Z3:Ast))
(define (init-vals ctx)
  (hasheq 'true  (mk-true ctx)
          'false (mk-false ctx)))

(: init-funs : Z3:Context → (HashTable Symbol Z3:Func))
(define (init-funs ctx)
  (hasheq))

(: init-sorts : Z3:Context → (HashTable Symbol Z3:Sort))
(define (init-sorts ctx)
  (hasheq 'Int  (mk-int-sort ctx)
          'Real (mk-real-sort ctx)
          'Bool (mk-bool-sort ctx)))

(: init-env : Z3:Context → Env)
(define (init-env ctx)
  (Env (init-vals ctx) (init-funs ctx) (init-sorts ctx)))

(: reset! : → Void)
(define (reset!)
  (define ctx (get-context))
  (define env (get-env))
  (set-Env-vals!  env (init-vals ctx))
  (set-Env-funs!  env (init-funs ctx))
  (set-Env-sorts! env (init-sorts ctx))
  (solver-reset! ctx (get-solver)))

(define-syntax-rule (with-local-push-pop e ...)
  (match-let ([(Env vals₀ funs₀ sorts₀) (get-env)]
              [ctx (get-context)]
              [solver (get-solver)])
    (begin0
        (let ()
          (solver-push! ctx solver)
          e ...)
      (solver-pop! (get-context) (get-solver) 1)
      (let ([env (get-env)])
        (set-Env-vals!  env vals₀)
        (set-Env-funs!  env funs₀)
        (set-Env-sorts! env sorts₀)))))
