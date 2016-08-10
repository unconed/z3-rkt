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
;; PN: Only have simple sorts for now, which makes it just simple lookup
(define (sort-expr->_z3-sort expr)
  (match expr
    [(? symbol? id)
     (define s (get-sort id))
     (if (z3-sort? s) s (-z3-null))]
    [(? z3-sort? expr) expr]
    [(? z3-null? expr) expr]
    [_ (error 'sort-expr->_z3-sort "unexpected: ~a" expr)]))

(: _z3-ast->expr : Z3:Ast → Any)
;; Given a Z3 AST, convert it to an expression that can be parsed again into an AST,
;; assuming the same context. This is the inverse of expr->_z3-ast above.
(define (_z3-ast->expr ast)
  (read (open-input-string (ast-to-string (ctx) ast))))

(: make-uninterpreted
   (case-> [String Null Any → Z3:Ast]
           [String (Pairof Any (Listof Any)) Any → Z3:Func]
           [String (Listof Any) Any → (U Z3:Ast Z3:Func)]))
;; Make an uninterpreted function given arg sorts and return sort.
(define (make-uninterpreted name argsorts retsort)
  (define cur-ctx (ctx))
  (define args (cast (map sort-expr->_z3-sort argsorts) (Listof Z3:Sort)))
  (define ret (tr:assert (sort-expr->_z3-sort retsort) z3-sort?))
  (cond [(null? argsorts)
         (app-to-ast cur-ctx (mk-fresh-const cur-ctx name ret))]
        [else
         (mk-func (mk-fresh-func-decl cur-ctx name args ret)
                      (string->symbol name)
                      (length argsorts))]))

(: dynamic-declare-fun
   (case-> [Symbol Null Any → Z3:Ast]
           [Symbol (Pairof Any (Listof Any)) Any → Z3:Func]
           [Symbol (Listof Any) Any → (U Z3:Ast Z3:Func)]))
;; Declare a new function. Each `D` is a sort-expr.
(define (dynamic-declare-fun f-id doms rng)
  (cond
    [(null? doms)
     (define v (make-uninterpreted (symbol->string f-id) '() rng))
     (set-val! f-id v)
     v]
    [else
     (define v (make-uninterpreted (symbol->string f-id) doms rng))
     (set-fun! f-id v)
     v]))

(: dynamic-declare-const : Symbol Any → Z3:Ast)
(define (dynamic-declare-const c-id rng) (dynamic-declare-fun c-id '() rng))

(define-simple-macro (declare-fun f:id (D ...) R)
  (define f (dynamic-declare-fun 'f '(D ...) 'R)))
(define-simple-macro (declare-const c:id T) (declare-fun c () T))

(define-syntax-rule (make-fun args ...)
  (make-uninterpreted "" 'args ...))

(define-syntax-rule (make-fun/vector n args ...)
  (for/vector : (Vectorof (U Z3:App Z3:Func)) ([i (in-range 0 n)])
    (make-uninterpreted "" 'args ...)))

(define-syntax-rule (make-fun/list n args ...)
  (for/list : (Listof (U Z3:App Z3:Func)) ([i (in-range 0 n)])
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
             (Listof (List (U Z3:Ast Z3:Func) Z3:Func (Listof Z3:Func)))))
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
    (for/list : (Listof (List (U Z3:Ast Z3:Func) Z3:Func (Listof Z3:Func)))
              ([constr constructors] [vr vrs])
      (define-values (K-name field-names)
        (match vr
          [(cons k flds) (values k (map (inst car Symbol Any) flds))]
          [(? symbol? k) (values k '())]))
      (define p-name (format-symbol "is-~a" K-name))
      (define-values (pre-K-decl p acs)
        (let-values ([(pre-K-decl p-decl ac-decls)
                      (query-constructor cur-ctx constr (length field-names))])
          (values pre-K-decl
                  (mk-func p-decl p-name 1)
                  (for/list : (Listof Z3:Func) ([ac-decl ac-decls] [field-name field-names])
                    (mk-func ac-decl field-name 1)))))
      (define K
        (if (null? field-names)
            (mk-app cur-ctx pre-K-decl)
            (mk-func pre-K-decl K-name (length field-names))))
      (if (z3-ast? K)
          (set-val! K-name K)
          (set-fun! K-name K))
      (set-fun! p-name p)
      (for ([field-name field-names] [ac acs])
        (set-fun! field-name ac))
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

(define-simple-macro (declare-datatype T:id vr:variant ...)
  (declare-datatypes () ((T vr ...))))

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
                     #`(begin
                         (define-values (#,K #,p)
                           (let-values ([(mk-K #,p _) (query-constructor cur-ctx #,con-K 0)])
                             (values (mk-app cur-ctx mk-K) (mk-func #,p '#,p 1))))
                         (set-val! '#,K #,K)
                         (set-fun! '#,p #,p)))]
                  [else
                   (define n (length accs))
                   #`(begin
                       (match-define-values (#,K #,p #,@accs)
                          (match-let-values ([(#,K #,p (list #,@accs))
                                              (query-constructor cur-ctx #,con-K #,(length accs))])
                            (values (mk-func #,K '#,K #,n)
                                    (mk-func #,p '#,p 1)
                                    #,@(for/list ([acc accs])
                                         #`(mk-func #,acc '#,acc 1)))))
                       (set-fun! '#,K #,K)
                       (set-fun! '#,p #,p)
                       #,@(for/list ([acc accs])
                            #`(set-fun! '#,acc #,acc)))]))))
     ;(printf "declare-datatypes:~n")
     ;(pretty-print (syntax->datum gen))
     gen]))

(: assert : Expr → Void)
(define (assert e)
  (assert-cnstr (ctx) (expr->_z3-ast e)))

(: check-sat : → Z3:Sat-LBool)
(define (check-sat)
  (define-values (rv model) (check-and-get-model (ctx)))
  (when model
    (set-current-model! model))
  rv)

(: smt:eval : Expr → Any)
(define (smt:eval expr)
  (eval-in-model (get-current-model) expr))

(: eval-in-model : Z3:Model Expr → Any)
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
   declare-datatypes
   declare-datatype dynamic-declare-datatype
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
