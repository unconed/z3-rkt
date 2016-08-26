#lang typed/racket/base

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse
                     racket/contract
                     racket/pretty)
         (prefix-in tr: (only-in typed/racket/base assert))
         racket/set
         racket/match
         racket/syntax
         racket/string
         syntax/parse/define
         "z3-wrapper.rkt"
         "environment.rkt"
         )
(require/typed racket/syntax
  [format-symbol (String Any * → Symbol)])

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

(: sort-expr->_z3-sort : Sort-Expr → Z3:Sort)
;; sort-exprs are sort ids, (_ id parameter*), or (id sort-expr*).
;; PN: Only have simple sorts for now, which makes it just simple lookup
(define (sort-expr->_z3-sort expr)
  (match expr
    [(? symbol? id) (get-sort id)]
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

(: dynamic-declare-sort : Symbol → Z3:Sort)
;; Declare a new sort.
(define (dynamic-declare-sort id)
  (define T (mk-uninterpreted-sort (get-context) (make-symbol id)))
  (new-sort! id T)
  T)

(: make-symbol : (U Symbol String) → Z3:Symbol)
;; Helper function to make a symbol with the given name (Racket symbol)
(define (make-symbol s)
  (cond [(string? s) (mk-string-symbol (get-context) s)]
        [else        (make-symbol (format "~a" s))]))
(define-simple-macro (declare-sort T:id) (dynamic-declare-sort 'T))

(: make-uninterpreted
   (case-> [String Null Sort-Expr → Z3:Ast]
           [String (Pairof Sort-Expr (Listof Sort-Expr)) Sort-Expr → Z3:Func]
           [String (Listof Sort-Expr) Sort-Expr → (U Z3:Ast Z3:Func)]))
;; Make an uninterpreted function given arg sorts and return sort.
(define (make-uninterpreted name argsorts retsort)
  (define cur-ctx (get-context))
  (define args (cast (map sort-expr->_z3-sort argsorts) (Listof Z3:Sort)))
  (define ret (assert (sort-expr->_z3-sort retsort) z3-sort?))
  (cond [(null? argsorts)
         (app-to-ast cur-ctx (mk-fresh-const cur-ctx name ret))]
        [else
         (mk-func (mk-fresh-func-decl cur-ctx name args ret)
                      (string->symbol name)
                      (length argsorts))]))

(: dynamic-declare-fun
   (case-> [Symbol Null Sort-Expr → Z3:Ast]
           [Symbol (Pairof Sort-Expr (Listof Sort-Expr)) Sort-Expr → Z3:Func]
           [Symbol (Listof Sort-Expr) Sort-Expr → (U Z3:Ast Z3:Func)]))
;; Declare a new function. Each `D` is a sort-expr.
(define (dynamic-declare-fun f-id doms rng)
  ;(log! (format "(declare-fun ~a ~a ~a)" f-id doms rng))
  (cond
    [(null? doms)
     (define v (make-uninterpreted (symbol->string f-id) '() rng))
     (set-val! f-id v)
     v]
    [else
     (define v (make-uninterpreted (symbol->string f-id) doms rng))
     (set-fun! f-id v)
     v]))

(: dynamic-declare-const : Symbol Sort-Expr → Z3:Ast)
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

(: constr->_z3-constructor :
   (Setof Symbol) Symbol (Listof (List Symbol (U Symbol Z3:Sort))) → Z3:Constructor)
(define (constr->_z3-constructor recursive-sort-names k field-list)
  (define names-sorts-refs
    (for/list : (Listof (List Z3:Symbol (U Z3:Sort Z3:Null) Nonnegative-Fixnum))
              ([field : (List Symbol (U Symbol Z3:Sort)) field-list])
      (match-define (list x t) field)
      (define nameᵢ (make-symbol x))
      (define sortᵢ
        (if (set-member? recursive-sort-names t)
            z3-null
            (sort-expr->_z3-sort t)))
      (define refᵢ 0)
      (list nameᵢ sortᵢ refᵢ)))
  (mk-constructor (get-context)
                  (make-symbol k)
                  (make-symbol (format "is-~a" k))
                  names-sorts-refs))

(: dynamic-declare-datatype :
   Symbol
   (Listof (U Symbol (Pairof Symbol (Listof (List Symbol (U Symbol Z3:Sort))))))
   → (Values Z3:Sort
             (Listof (List (U Z3:Ast Z3:Func) Z3:Func (Listof Z3:Func)))))
;; TODO: type parameters
(define (dynamic-declare-datatype T-id vrs)
  (define cur-ctx (get-context))

  ;; create constructors
  (define constructors
    (for/list : (Listof Z3:Constructor) ([vr vrs])
      (match vr
        [(cons k flds) (constr->_z3-constructor {seteq T-id} k flds)]
        [(? symbol? k) (constr->_z3-constructor {seteq T-id} k '())])))

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
           (define cur-ctx (get-context))
           
           ;; create constructors
           #,@(for/list ([con-K      (in-list con-Ks)]
                         [K          (in-list Ks)]
                         [field-list (in-list field-lists)])
                #`(define #,con-K (constr->_z3-constructor {seteq 'T} '#,K '#,field-list)))
           
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

(: assert! : Expr → Void)
(define (assert! e)
  (define ast (expr->_z3-ast e))
  ;(log! (format "(assert ~a)" (ast-to-string (get-context) ast)))
  (solver-assert! (get-context) (get-solver) ast))

(: check-sat : → Z3:LBool)
(define (check-sat)
  ;(log! "(check-sat)")
  (solver-check (get-context) (get-solver)))

(: get-model : → Z3:Model)
(define (get-model)
  (solver-get-model (get-context) (get-solver)))

(: get-stats : → (HashTable Symbol Real))
(define (get-stats)
  (define ctx (get-context))
  (define solver (get-solver))
  (define stats (solver-get-statistics ctx solver))
  (begin0
      (begin
        (stats-inc-ref! ctx stats)
        (for/hasheq : (HashTable Symbol Real) ([i (stats-size ctx stats)])
          (define k (string->symbol (string-replace (stats-get-key ctx stats i) " " "-")))
          (define v
            (cond [(stats-is-uint? ctx stats i)
                   (stats-get-uint-value ctx stats i)]
                  [else
                   (stats-get-double-value ctx stats i)]))
          (values k v)))
    (stats-dec-ref! ctx stats)))

;; XXX need to implement a function to get all models. To do that we need
;; push, pop, and a way to navigate a model.

(provide
 expr->_z3-ast
 sort-expr->_z3-sort
 (combine-out ; remove smt: for now
  declare-datatypes
  declare-datatype dynamic-declare-datatype
  declare-sort dynamic-declare-sort
  declare-const dynamic-declare-const
  declare-fun dynamic-declare-fun
  ;make-fun
  ;make-fun/vector
  ;make-fun/list
  assert!
  check-sat
  get-model
  get-stats)
 ; XXX move these to a submodule once Racket 5.3 is released
 (prefix-out smt:internal:
             (combine-out
              make-symbol)))
