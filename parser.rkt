#lang racket/base

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse
                     racket/contract
                     racket/pretty)
         racket/match
         racket/contract
         racket/syntax
         syntax/parse/define
         "utils.rkt"
         (prefix-in z3: "z3-wrapper.rkt")
         )

;; Handle the next error.
(define (handle-next-error)
  (define err (z3:get-error-code (ctx)))
  (raise-user-error "~s" (z3:get-error-msg err)))

;; Set the logic for this context. This can only be called once.
(define (set-logic logic)
  (unless (z3:set-logic (ctx) (symbol->string logic))
    (handle-next-error)))

;; Declare a new sort.
(define-simple-macro (declare-sort T:id)
  ;; PN: should this be `new-sort!`?
  (new-sort! 'T (z3:mk-uninterpreted-sort (ctx) (make-symbol 'T))))

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
          (get-or-create-instance sort (map sort-expr->_z3-sort args)))
         (apply sort (map sort-expr->_z3-sort args)))]
    [id
     (cond [(get-sort id) => values]
           [else (z3:-z3-null)])]))

;; Given a Z3 AST, convert it to an expression that can be parsed again into an AST,
;; assuming the same context. This is the inverse of expr->_z3-ast above.
;; PN: How does this handle the `@app` thing?
(define (_z3-ast->expr ast)
  (read (open-input-string (z3:ast-to-string (ctx) ast))))

;; Make an uninterpreted function given arg sorts and return sort.
(define (make-uninterpreted name argsorts retsort)
  (define args (map sort-expr->_z3-sort argsorts))
  (define ret (sort-expr->_z3-sort retsort))
  (cond [(null? args) (z3:mk-fresh-const     (ctx) name      ret)]
        [else         (z3:mk-fresh-func-decl (ctx) name args ret)]))

;; Declare a new function. Each `D` is a sort-expr.
(define-simple-macro (declare-fun f:id (D ...) R)
  (define f (make-uninterpreted (symbol->string 'f) '(D ...) 'R)))
(define-simple-macro (declare-const c:id T) (declare-fun c () T))

(define-syntax-rule (make-fun args ...)
  (make-uninterpreted "" 'args ...))

(define-syntax-rule (make-fun/vector n args ...)
  (for/vector ([i (in-range 0 n)])
    (make-uninterpreted "" 'args ...)))

(define-syntax-rule (make-fun/list n args ...)
  (for/list ([i (in-range 0 n)])
    (make-uninterpreted "" 'args ...)))

;; Helper function to make a symbol with the given name (Racket symbol)
(define/contract (make-symbol s)
  ((or/c symbol? string?) . -> . z3:z3-symbol?)
  (cond [(string? s) (z3:mk-string-symbol (ctx) s)]
        [else        (make-symbol (format "~a" s))]))

(define/contract (constr->_z3-constructor k field-list)
  (symbol? (listof (list/c symbol? symbol?)) . -> . z3:z3-constructor?)
  (match-define `([,x ,t] ...) field-list)
  (define names-sorts-refs
    (for/list ([xᵢ (in-list x)] [tᵢ (in-list t)])
      (define nameᵢ (make-symbol xᵢ))
      (define sortᵢ (sort-expr->_z3-sort tᵢ))
      (define refᵢ 0)
      (list nameᵢ sortᵢ refᵢ)))
  (z3:mk-constructor (ctx)
                     (make-symbol k)
                     (make-symbol (format "is-~a" k))
                     names-sorts-refs))

(begin-for-syntax
  (define-syntax-class fld
    #:description "field"
    (pattern (name:id typ:id)))

  (define-syntax-class variant
    #:description "datatype variant"
    (pattern name:id)
    (pattern (name:id field:fld ...))))

;; Declare a complex datatype.
;; TODO: handle type parameters
;; TODO: handle mutually recursive types
;; TODO: should I use "/s" suffix to stay consistent with builtin ones?
;;       If these are limited in (with-context ...), probably no need
(define-syntax (declare-datatypes stx)
  (syntax-parse stx
    ;; My attempt at ADT
    [(_ () ((T:id vr:variant ...)))
     (define/contract (parse-vr vr)
       (syntax? . -> . (values identifier?      ; (internal) constructor
                               identifier?      ; constructor
                               (listof syntax?) ; accesstor × type …
                               ))
       (syntax-parse vr
         [K:id (parse-vr #'(K))]
         [(K:id [x:id t] ...)
          (values (format-id #'K "con-~a" (syntax->datum #'K))
                  #'K
                  (syntax->list #'((x t) ...)))]))

     (define-values (con-Ks Ks field-lists)
       (for/lists (con-Ks Ks field-lists)
                  ([vr (syntax->list #'(vr ...))])
         (parse-vr vr)))
     
     (define gen
       #`(begin
           (define cur-ctx (ctx))
           
           ;; create constructors
           #,@(for/list ([con-K      (in-list con-Ks)]
                         [K          (in-list Ks)]
                         [field-list (in-list field-lists)])
                #`(define #,con-K (constr->_z3-constructor '#,K '#,field-list)))
           
           ;; define datatype
           (define T (z3:mk-datatype cur-ctx (make-symbol 'T) (list #,@con-Ks)))
           (new-sort! 'T T)

           ;; define constructor/tester/accessors for each variant
           #,@(for/list ([con-K      (in-list con-Ks)]
                         [K          (in-list Ks)]
                         [field-list (in-list field-lists)])
                (define p     (format-id K "is-~a"  (syntax->datum K)))
                (define accs
                  (for/list ([field field-list])
                    (syntax-parse field
                      [(x:id t) #'x])))
                (cond
                  [(null? accs)
                   (with-syntax ([mk-K (format-id K "mk-~a" (syntax->datum K))])
                     #`(define-values (#,K #,p)
                         (let-values ([(mk-K #,p _) (z3:query-constructor cur-ctx #,con-K 0)])
                           (values (mk-K) #,p))))]
                  [else
                   #`(match-define-values (#,K #,p (list #,@accs))
                                          (z3:query-constructor cur-ctx #,con-K #,(length accs)))]))))
     ;(printf "declare-datatypes:~n")
     ;(pretty-print (syntax->datum gen))
     gen]))

(define (assert e)
  (z3:assert-cnstr (ctx) (z3:expr->_z3-ast e)))

(define (check-sat)
  (define-values (rv model) (z3:check-and-get-model (ctx)))
  (set-current-model! model)
  rv)

(define (eval-in-model model expr)
  (match/values (z3:eval (ctx) model (z3:expr->_z3-ast expr))
    [((? values) ast) (_z3-ast->expr ast)]
    [(_          _  ) (error 'eval-in-model "Evaluation failed")]))

(define (smt:eval expr)
  (eval-in-model (get-current-model) expr))

(define-syntax-rule (with-context info body ...)
  (parameterize ([current-context-info info])
    body ...))

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
   (rename-out [get-current-model get-model])))
 smt:eval
 (prefix-out smt: (contract-out
                   [set-logic (-> symbol? any)]))
 ; XXX move these to a submodule once Racket 5.3 is released
 (prefix-out smt:internal:
             (combine-out
              make-symbol
              sort-expr->_z3-sort)))
