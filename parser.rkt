#lang typed/racket/base

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse
                     racket/contract
                     racket/pretty)
         (prefix-in tr: (only-in typed/racket/base assert))
         racket/match
         racket/syntax
         syntax/parse/define
         (except-in "z3-wrapper.rkt" set-logic)
         (prefix-in z3: (only-in "z3-wrapper.rkt" set-logic))
         )
(require/typed racket/syntax
  [format-symbol (String Any * → Symbol)])

(: handle-next-error : → Nothing)
;; Handle the next error.
(define (handle-next-error)
  (define err (get-error-code (ctx)))
  (raise-user-error "~s" (get-error-msg err)))

(: set-logic : #|TODO|# Symbol → Void)
;; Set the logic for this context. This can only be called once.
(define (set-logic logic)
  (unless (z3:set-logic (ctx) (symbol->string logic))
    (handle-next-error)))

(: dynamic-declare-sort : Symbol → Z3:Sort)
;; Declare a new sort.
(define (dynamic-declare-sort id)
  (define T (mk-uninterpreted-sort (ctx) (make-symbol id)))
  (new-sort! id T)
  T)

(: make-symbol : (U Symbol String) → Z3:Symbol)
;; Helper function to make a symbol with the given name (Racket symbol)
(define (make-symbol s)
  (cond [(string? s) (mk-string-symbol (ctx) s)]
        [else        (make-symbol (format "~a" s))]))
(define-simple-macro (declare-sort T:id) (dynamic-declare-sort 'T))

(: sort-expr->_z3-sort : Any → (U Z3:Sort Z3:Null))
;; sort-exprs are sort ids, (_ id parameter*), or (id sort-expr*).
(define (sort-expr->_z3-sort expr)
  (match expr
    [(list '_ (? symbol? id) params ...)
     (define sort (get-sort id))
     (cond
       [(procedure? sort) (apply (cast sort (Any * → Z3:Sort)) params)]
       [else (error 'sort-expr->_z3-sort "unexpected")])]
    [(list (? symbol? id) args ...)
     (define sort (get-sort id))
     ;; The sort can either be a complex sort which needs to be
     ;; instantiated, or a simple array sort.
     (cond
       [(z3-complex-sort? sort)
        (datatype-instance-z3-sort
          (get-or-create-instance sort (map sort-expr->_z3-sort args)))]
       [else
        (apply (cast sort (Any * → Z3:Sort)) (map sort-expr->_z3-sort args))])]
    [(? symbol? id)
     (define sort (get-sort id))
     (cond [(z3-sort? sort) sort]
           [else (-z3-null)])]))

(: _z3-ast->expr : Z3:Ast → Any)
;; Given a Z3 AST, convert it to an expression that can be parsed again into an AST,
;; assuming the same context. This is the inverse of expr->_z3-ast above.
(define (_z3-ast->expr ast)
  (read (open-input-string (ast-to-string (ctx) ast))))

(: make-uninterpreted
   (case-> [String Null TODO → Z3:App]
           [String (Pairof TODO (Listof TODO)) TODO → Z3:Func-Decl]
           [String (Listof TODO) TODO → (U Z3:App Z3:Func-Decl)]))
;; Make an uninterpreted function given arg sorts and return sort.
(define (make-uninterpreted name argsorts retsort)
  (define args (cast (map sort-expr->_z3-sort argsorts) (Listof Z3:Sort)))
  (define ret (tr:assert (sort-expr->_z3-sort retsort) z3-sort?))
  (cond [(null? argsorts) (mk-fresh-const     (ctx) name      ret)]
        [else             (mk-fresh-func-decl (ctx) name args ret)]))

(: dynamic-declare-fun
   (case-> [Symbol Null TODO → Z3:App]
           [Symbol (Pairof TODO (Listof TODO)) TODO → Z3:Func-Decl]
           [Symbol (Listof TODO) TODO → (U Z3:App Z3:Func-Decl)]))
;; Declare a new function. Each `D` is a sort-expr.
(define (dynamic-declare-fun f-id doms rng)
  (define f (make-uninterpreted (symbol->string f-id) doms rng))
  (set-value! f-id f)
  f)

(: dynamic-declare-const : Symbol TODO → Z3:App)
(define (dynamic-declare-const c-id rng) (dynamic-declare-fun c-id '() rng))

(define-simple-macro (declare-fun f:id (D ...) R)
  (define f (dynamic-declare-fun 'f '(D ...) 'R)))
(define-simple-macro (declare-const c:id T) (declare-fun c () T))

(define-syntax-rule (make-fun args ...)
  (make-uninterpreted "" 'args ...))

(define-syntax-rule (make-fun/vector n args ...)
  (for/vector : (Vectorof (U Z3:App Z3:Func-Decl)) ([i (in-range 0 n)])
    (make-uninterpreted "" 'args ...)))

(define-syntax-rule (make-fun/list n args ...)
  (for/list : (Listof (U Z3:App Z3:Func-Decl)) ([i (in-range 0 n)])
    (make-uninterpreted "" 'args ...)))

(: constr->_z3-constructor : Symbol (Listof (List Symbol Symbol)) → Z3:Constructor)
(define (constr->_z3-constructor k field-list)
  (define names-sorts-refs
    (for/list : (Listof (List Z3:Symbol (U Z3:Sort Z3:Null) Nonnegative-Fixnum)) ([field field-list])
      (match-define (list x t) field)
      (define nameᵢ (make-symbol x))
      (define sortᵢ (sort-expr->_z3-sort t))
      (define refᵢ 0)
      (list nameᵢ sortᵢ refᵢ)))
  (mk-constructor (ctx)
                  (make-symbol k)
                  (make-symbol (format "is-~a" k))
                  names-sorts-refs))

(: dynamic-declare-datatype :
   Symbol
   (Listof (U Symbol (Pairof Symbol (Listof (List Symbol Symbol)))))
   → (Values Z3:Sort
             (Listof (List (U Z3:Ast Z3:Func-Decl)
                           (Z3:Ast → Z3:Ast)
                           (Listof (Z3:Ast → Z3:Ast))))))
;; TODO: type parameters
(define (dynamic-declare-datatype T-id vrs)
  (define cur-ctx (ctx))

  ;; create constructors
  (define constructors
    (for/list : (Listof Z3:Constructor) ([vr vrs])
      (match vr
        [(cons k flds) (constr->_z3-constructor k flds)]
        [(? symbol? k)   (constr->_z3-constructor k '())])))

  ;; define datatype
  (define T (mk-datatype cur-ctx (make-symbol T-id) constructors))
  (new-sort! T-id T)
  
  ;; define constructor/tester/accessors for each variant
  (define variants
    (for/list : (Listof (List (U Z3:Ast Z3:Func-Decl)
                              (Z3:Ast → Z3:Ast)
                              (Listof (Z3:Ast → Z3:Ast))))
              ([constr constructors] [vr vrs])
      (define-values (K-name field-names)
        (match vr
          [(cons k flds) (values k (map (inst car Symbol Any) flds))]
          [(? symbol? k) (values k '())]))
      (define-values (pre-K p acs) (query-constructor cur-ctx constr (length field-names)))
      (define K (if (null? field-names) (pre-K) pre-K))
      
      (set-value! K-name K)
      (set-value! (format-symbol "is-~a" K-name) p)
      (for ([field-name field-names] [ac acs])
        (set-value! field-name ac))

      (list K p acs)))
  
  (values T variants))

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
           (define T (mk-datatype cur-ctx (make-symbol 'T) (list #,@con-Ks)))
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
                         (let-values ([(mk-K #,p _) (query-constructor cur-ctx #,con-K 0)])
                           (values (mk-K) #,p))))]
                  [else
                   #`(match-define-values (#,K #,p (list #,@accs))
                                          (query-constructor cur-ctx #,con-K #,(length accs)))]))))
     ;(printf "declare-datatypes:~n")
     ;(pretty-print (syntax->datum gen))
     gen]))

(: assert : Any → Void)
(define (assert e)
  (printf "assert: ~a~n" e)
  (assert-cnstr (ctx) (expr->_z3-ast e)))

(: check-sat : → Z3:Sat-LBool)
(define (check-sat)
  (define-values (rv model) (check-and-get-model (ctx)))
  (when model
    (set-current-model! model))
  rv)

(: smt:eval : Any → Any)
(define (smt:eval expr)
  (eval-in-model (get-current-model) expr))

(: eval-in-model : Z3:Model Any → Any)
(define (eval-in-model model expr)
  (match/values (eval (ctx) model (expr->_z3-ast expr))
    [((? values) (? values ast)) (_z3-ast->expr ast)]
    [(_          _             ) (error 'eval-in-model "Evaluation failed")]))

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
   declare-datatypes dynamic-declare-datatype
   declare-sort dynamic-declare-sort
   declare-const dynamic-declare-const
   declare-fun dynamic-declare-fun
   make-fun
   make-fun/vector
   make-fun/list
   assert
   check-sat
   (rename-out [get-current-model get-model])))
 smt:eval
 (prefix-out smt: set-logic)
 ; XXX move these to a submodule once Racket 5.3 is released
 (prefix-out smt:internal:
             (combine-out
              make-symbol
              sort-expr->_z3-sort)))
