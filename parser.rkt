#lang racket/base

(require (for-syntax racket/base
                     syntax/parse)
         racket/match
         racket/contract
         "utils.rkt"
         (prefix-in z3: "z3-wrapper.rkt")
         )

(define (get-value id)
  (hash-ref (z3ctx-vals (current-context-info)) id))
(define (set-value! id v)
  (hash-set! (z3ctx-vals (current-context-info)) id v))

;; The current model for this context. This is a mutable box.
(define (get-current-model)
  (cond
    [(unbox (z3ctx-current-model (current-context-info))) => values]
    [else (error 'get-current-model "No model found")]))
(define (set-current-model! new-model)
  (set-box! (z3ctx-current-model (current-context-info)) new-model))

(define-syntax-rule (with-context info body ...)
  (parameterize ([current-context-info info])
    body ...))

;; Handle the next error.
(define (handle-next-error)
  (define err (z3:get-error-code (ctx)))
  (raise-user-error "~s" (z3:get-error-msg err)))

;; Set the logic for this context. This can only be called once.
(define (set-logic logic)
  (unless (z3:set-logic (ctx) (symbol->string logic))
    (handle-next-error)))

;; Declare a new sort. num-params is currently ignored.
(define-syntax-rule (declare-sort sort num-params)
  (set-value! 'sort (z3:mk-uninterpreted-sort (ctx) (make-symbol 'sort))))

;; sort-exprs are sort ids, (_ id parameter*), or (id sort-expr*).
(define (sort-expr->_z3-sort expr)
  (match expr
    [(list '_ id params ...) (apply (get-sort id) params)]
    [(list id args ...)
     (define sort (get-sort id))
     ;; The sort can either be a complex sort which needs to be
     ;; instantiated, or a simple array sort.
     (if (z3-complex-sort? sort)
         (datatype-instance-z3-sort
          (get-or-create-instance (get-sort id) (map sort-expr->_z3-sort args)))
         (apply sort (map sort-expr->_z3-sort args)))]
    [id (get-sort id)]))

;; Given an expr, convert it to a Z3 AST. This is a really simple recursive descent parser.
(define (expr->_z3-ast expr)
  ;(displayln (format "IN: ~a" expr))
  (define cur-ctx (ctx))
  (define ast
    (let go ([expr expr])
      (match expr
        ; Non-basic expressions
        [(list '@app (? symbol? fn-name) args ...)
         (apply (get-value fn-name) cur-ctx (map go args))]
        [(list '@app proc args ...)
         (apply proc cur-ctx (map go args))]
        ; Numerals
        [(? exact-integer?) (z3:mk-numeral cur-ctx (number->string expr) (get-sort 'Int))]
        [(? inexact-real?) (z3:mk-numeral cur-ctx (number->string expr) (get-sort 'Real))]
        ; Booleans
        [#t (get-value 'true)]
        [#f (get-value 'false)]
        ; Symbols
        [(? symbol?) (get-value expr)]
        ; Anything else
        [_ expr])))
  ;(displayln (format "Output: ~a ~a ~a" expr ast (z3:ast-to-string (ctx) ast)))
  ast)

;; Given a Z3 AST, convert it to an expression that can be parsed again into an AST,
;; assuming the same context. This is the inverse of expr->_z3-ast above.
(define (_z3-ast->expr ast)
  (read (open-input-string (z3:ast-to-string (ctx) ast))))

;; Make an uninterpreted function given arg sorts and return sort.
(define (make-uninterpreted name argsorts retsort)
  (define args (map sort-expr->_z3-sort argsorts))
  (define ret (sort-expr->_z3-sort retsort))
  (cond [(null? args) (z3:mk-fresh-const     (ctx) name      ret)]
        [else         (z3:mk-fresh-func-decl (ctx) name args ret)]))

;; Declare a new function. argsort is a sort-expr.
(define-syntax-rule (declare-fun fn args ret)
  (define fn (make-uninterpreted (symbol->string 'fn) 'args 'ret)))

(define-syntax-rule (declare-const c T) (declare-fun c () T))

(define-syntax-rule (make-fun args ...)
  (make-uninterpreted "" 'args ...))

(define-syntax-rule (make-fun/vector n args ...)
  (for/vector ([i (in-range 0 n)])
    (make-uninterpreted "" 'args ...)))

(define-syntax-rule (make-fun/list n args ...)
  (for/list ([i (in-range 0 n)])
    (make-uninterpreted "" 'args ...)))

;; Helper function to make a symbol with the given name (Racket symbol)
(define/contract (make-symbol symbol-name)
  ((or/c symbol? string?) . -> . #|cpointer/c _z3-symbol|# any)
  (cond [(string? symbol-name) (z3:mk-string-symbol (ctx) symbol-name)]
        [else (make-symbol (format "~a" symbol-name))]))

(define/contract (constr->_z3-constructor k)
  (symbol? . -> . #|_z3-constructor|# any)
  (z3:mk-constructor (ctx)
                     (make-symbol k)
                     (make-symbol (format "is-~a" k))
                     '()))

;; Declare a complex datatype. Currently one scalar type is supported.
;; param-types is currently ignored
(define-syntax (declare-datatypes stx)
  (syntax-parse stx
    ;; Scala case in original code
    [(_ param-types ((stx-typename:id stx-args:id ...)))
     #'(let* ([typename 'stx-typename]
              [args (list 'stx-args ...)]
              [constrs (map constr->_z3-constructor args)]
              [datatype (z3:mk-datatype (ctx) (make-symbol typename) constrs)])
         (new-sort! typename datatype)
         (for ([constr-name (in-list args   )]
               [constr      (in-list constrs)])
           ;; TODO handle > 0
           (define-values (constr-fn tester-fn accessor-fns) (z3:query-constructor (ctx) constr 0))
           (set-value! constr-name (z3:mk-app (ctx) constr-fn))))]
    ;; My attempt at ADT
    ))

(define (assert expr)
  (z3:assert-cnstr (ctx) (expr->_z3-ast expr)))

(define (check-sat)
  (define-values (rv model) (z3:check-and-get-model (ctx)))
  (set-current-model! model)
  rv)

(define get-model get-current-model)

(define (eval-in-model model expr)
  (match/values (z3:eval (ctx) model (expr->_z3-ast expr))
    [((? values) ast) (_z3-ast->expr ast)]
    [(_          _  ) (error 'eval-in-model "Evaluation failed")]))

(define (smt:eval expr)
  (eval-in-model (get-current-model) expr))

;; XXX need to implement a function to get all models. To do that we need
;; push, pop, and a way to navigate a model.

(provide
 (prefix-out
  smt:
  (combine-out
   with-context
   declare-datatypes
   declare-sort
   declare-const
   declare-fun
   make-fun
   make-fun/vector
   make-fun/list
   assert
   check-sat
   get-model))
 smt:eval
 (prefix-out smt: (contract-out
                   [set-logic (-> symbol? any)]))
 ; XXX move these to a submodule once Racket 5.3 is released
 (prefix-out smt:internal:
             (combine-out
              make-symbol
              sort-expr->_z3-sort)))
