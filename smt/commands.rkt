#lang typed/racket/base

(provide
 with-new-context
 init-global-context!
 destroy-global-context!
 with-local-stack
 get-val
 get-fun
 get-sort
 
 declare-datatypes
 declare-datatype
 dynamic-declare-datatype
 declare-sort
 dynamic-declare-sort
 declare-const
 dynamic-declare-const
 declare-fun
 dynamic-declare-fun
 assert!
 check-sat
 check-sat/model
 get-stats
 pattern-of

 print-current-assertions

 define-fun
 define-const
 )

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse
                     racket/contract
                     racket/pretty)
         racket/set
         racket/match
         racket/syntax
         racket/string
         syntax/parse/define
         "../ffi/main.rkt"
         "private.rkt"
         "primitives.rkt"
         )
(require/typed racket/syntax
  [format-symbol (String Any * → Symbol)])

(: dynamic-declare-sort : Symbol → Z3:Sort)
;; Declare a new sort.
(define (dynamic-declare-sort id)
  (define T (mk-uninterpreted-sort (get-context) (make-symbol id)))
  (new-sort! id T)
  T)

(define-simple-macro (declare-sort T:id) (define T (dynamic-declare-sort 'T)))

(: dynamic-declare-fun
   (case-> [Symbol Null Sort-Expr → Z3:Ast]
           [Symbol (Pairof Sort-Expr (Listof Sort-Expr)) Sort-Expr → Z3:Func]
           [Symbol (Listof Sort-Expr) Sort-Expr → (U Z3:Ast Z3:Func)]))
;; Declare a new function. Each `D` is a sort-expr.
(define (dynamic-declare-fun f-id dom rng)
  (define ctx (get-context))
  (define name (make-symbol f-id))
  (define rng-sort (assert (sort-expr->_z3-sort rng) z3-sort?))
  (cond
    [(null? dom)
     (define v (app-to-ast ctx (mk-const ctx name rng-sort)))
     (set-val! f-id v)
     v]
    [else
     (define dom-sorts (cast (map sort-expr->_z3-sort dom) (Listof Z3:Sort)))
     (define v (mk-func (mk-func-decl ctx name dom-sorts rng-sort)
                        f-id
                        (length dom)))
     (set-fun! f-id v)
     v]))

(: dynamic-declare-const : Symbol Sort-Expr → Z3:Ast)
(define (dynamic-declare-const c-id rng) (dynamic-declare-fun c-id '() rng))

(define-simple-macro (declare-fun f:id (D ...) R)
  (define f (dynamic-declare-fun 'f (list D ...) R)))
(define-simple-macro (declare-const c:id T) (declare-fun c () T))

(: constr->_z3-constructor :
   (Setof Symbol) Symbol (Listof (List Symbol Sort-Expr)) → Z3:Constructor)
(define (constr->_z3-constructor recursive-sort-names k field-list)
  (define names-sorts-refs
    (for/list : (Listof (List Z3:Symbol (U Z3:Sort Z3:Null) Nonnegative-Fixnum))
              ([field : (List Symbol Sort-Expr) field-list])
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
  
  ;; TODO: make sure this is safe
  (for ([c constructors]) (del-constructor cur-ctx c))
  
  (values T variants))

(begin-for-syntax
  (define-syntax-class fld
    #:description "field"
    (pattern (name:id typ)))

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
                (let ([fields
                       (for/list ([field-dec field-list])
                         (syntax-parse field-dec
                           [(x:id t) #'(list 'x t)]))])
                  #`(define #,con-K
                      (constr->_z3-constructor {seteq 'T} '#,K (list #,@fields)))))
           
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
                       (del-constructor cur-ctx #,con-K) ; TODO make sure it's safe
                       (set-fun! '#,K #,K)
                       (set-fun! '#,p #,p)
                       #,@(for/list ([acc accs])
                            #`(set-fun! '#,acc #,acc)))]))))
     ;(printf "declare-datatypes:~n")
     ;(pretty-print (syntax->datum gen))
     gen]))

(: assert! : Expr → Void)
(define (assert! e)
  (solver-assert! (get-context) (get-solver) (expr->_z3-ast e)))

(: check-sat : → Z3:Sat-LBool)
(define (check-sat)
  (case (solver-check (get-context) (get-solver))
    [(true) 'sat]
    [(false) 'unsat]
    [(undef) 'unknown]))

(: check-sat/model : → (U Z3:Model 'unsat 'unknown))
(define (check-sat/model)
  (case (solver-check (get-context) (get-solver))
    [(true) (solver-get-model (get-context) (get-solver))]
    [(false) 'unsat]
    [(undef) 'unknown]))

(: pattern-of : Z3:Ast Z3:Ast * → Z3:Pattern)
(define (pattern-of ast . asts)
  (apply mk-pattern (get-context) ast asts))

(: get-stats : → (HashTable Symbol (U Inexact-Real Nonnegative-Fixnum)))
(define (get-stats)
  (define ctx (get-context))
  (define solver (get-solver))
  (define stats (solver-get-statistics ctx solver))
  (begin0
      (begin
        (stats-inc-ref! ctx stats)
        (for/hasheq : (HashTable Symbol (U Inexact-Real Nonnegative-Fixnum)) ([i (stats-size ctx stats)])
          (define k (string->symbol (string-replace (stats-get-key ctx stats i) " " "-")))
          (define v
            (cond [(stats-is-uint? ctx stats i)
                   (stats-get-uint-value ctx stats i)]
                  [else
                   (stats-get-double-value ctx stats i)]))
          (values k v)))
    (stats-dec-ref! ctx stats)))

(: print-current-assertions : → Void)
(define (print-current-assertions)
  (define ctx (get-context))
  (define assertions (solver-get-assertions ctx (get-solver)))
  (for ([i (ast-vector-size ctx assertions)])
    (printf "~a~n" (ast-to-string ctx (ast-vector-get ctx assertions i)))))


;; Functions that are written in terms of the base functions in main.rkt and
;; builtins.rkt.

;; Define a function using universal quantifiers as a sort of macro.
;; Note that defining recursive functions is possible but highly
;; recommended against.
(define-syntax (define-fun stx)
  (syntax-parse stx
    [(_ c:id () T e)
     #'(begin
       (declare-const c T)
       (assert! (=/s c e)))]
    [(_ f:id ([x:id Tx] ...) T e)
     ;; FIXME: This can cause exponential blowup.
     ;; But I can't figure out how to use `macro-finder` from C API for now
     (define n (length (syntax->list #'(x ...))))
     #`(begin
         (define f : Z3:Func
           (let ([m : (HashTable (Listof Expr) Z3:Ast) (make-hash)])
             (match-lambda*
               [(and xs (list x ...))
                (hash-ref! m xs (λ () e))]
               [xs
                (error 'f "wrong arity. Expect ~a, given ~a arguments" #,n (length xs))])))
         (set-fun! 'f f))
     #;#'(begin
       (smt:declare-fun f (Tx ...) T)
       (smt:assert (∀/s ([x Tx] ...) (=/s (f x ...) e))))]))
(define-simple-macro (define-const c:id T e) (define-fun c:id () T e))
