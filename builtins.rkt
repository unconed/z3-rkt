#lang typed/racket/base

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse
                     racket/contract)
         racket/list
         racket/match
         (only-in racket/function curry)
         syntax/parse/define
         "parser.rkt"
         "z3-wrapper.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Utils (from old `utils.rkt`)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This is the prototype namespace for new contexts. It is added to by
;; define-builtin-symbol and define-builtin-proc below.
(define builtin-vals-eval-at-init : (HashTable Symbol (Z3:Context → Z3:Ast)) (make-hasheq))
(define builtin-sorts             : (HashTable Symbol (Z3:Context → Z3:Sort)) (make-hasheq))

(begin-for-syntax
  
  (define/contract (add-smt-suffix id)
    (identifier? . -> . identifier?)
    (format-id id "~a/s" (syntax->datum id)))
  
  (define-syntax-class arity
    #:description "function arity (natural or *)"
    (pattern (~or n:nat (~literal *) (~literal lassoc) (~literal rassoc)))))

(define-syntax (define-builtin-symbol stx)
  (syntax-parse stx
    [(_ c:id v)
     (with-syntax ([c/s (add-smt-suffix #'c)])
       #'(begin
           ; PN: why not assign `v` to it?
           ; --> because there's always `ctx` that needs passing in
           (define c/s 'c)
           (hash-set! builtin-vals-eval-at-init 'c v)
           (provide c/s)))]))

(define-syntax (define-builtin-proc stx)
  (syntax-parse stx
    [(_ f:id v n:arity)
     (with-syntax ([f/s (add-smt-suffix #'f)])
       (syntax-parse #'n
         [k:nat
          (with-syntax ([(x ...)
                         (datum->syntax
                          #f
                          (build-list (syntax->datum #'k)
                                      (λ (i) (format-id #f "x~a" i))))])
            #'(begin
                (define (f/s [x : Expr] ...)
                  #;(printf "Applying ~a to ~a~n"
                          'f/s
                          (list `(,(ast-to-string (ctx) (expr->_z3-ast x)) :
                                  ,(sort-to-string (ctx) (z3-get-sort (ctx) (expr->_z3-ast x)))) ...))
                  (v (ctx) (expr->_z3-ast x) ...))
                (provide f/s)))]
         [(~literal *)
          #'(begin
              (define (f/s . [xs : Expr *])
                (define args (map expr->_z3-ast xs))
                #;(printf "Applying ~a to ~a~n"
                          'f/s
                          (for/list : (Listof String) ([arg args])
                            (ast-to-string (ctx) arg)))
                (apply v (ctx) (map expr->_z3-ast xs)))
              (provide f/s))]
         [(~literal lassoc)
          #'(begin
              (define f/s
                (lassoc
                 (λ ([x : Expr] [y : Expr])
                   ;; TODO just debugging
                   #;(printf "Applying ~a to ~a, ~a~n"
                           'f/s
                           (ast-to-string (ctx) (expr->_z3-ast x))
                           (ast-to-string (ctx) (expr->_z3-ast y)))
                   (v (ctx) (expr->_z3-ast x) (expr->_z3-ast y)))))
              (provide f/s))]
         [(~literal rassoc)
          #'(begin
              (define f/s
                (rassoc
                 (λ ([x : Expr] [y : Expr])
                   ;; TODO just debugging
                   #;(printf "Applying ~a to ~a, ~a~n"
                           'f/s
                           (ast-to-string (ctx) (expr->_z3-ast x))
                           (ast-to-string (ctx) (expr->_z3-ast y)))
                   (v (ctx) (expr->_z3-ast x) (expr->_z3-ast y)))))
              (provide f/s))]))]))

(define-simple-macro (define-builtin-sort x:id v)
  (hash-set! builtin-sorts 'x v))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; from old `builtins.rkt`
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Initialize builtins.
(: init-builtins : Z3:Context → (Values (HashTable Symbol Z3:Ast)
                                        (HashTable Symbol Z3:Func)
                                        (HashTable Symbol Z3:Sort)))
(define (init-builtins cur-ctx)
  (values
   (for/hasheq : (HashTable Symbol Z3:Ast) ([(k fn) (in-hash builtin-vals-eval-at-init)])
     (values k (fn cur-ctx)))
   (hasheq)
   (for/hasheq : (HashTable Symbol Z3:Sort) ([(k fn) (in-hash builtin-sorts)])
     (values k (fn cur-ctx)))))
(provide init-builtins)

(define int-list-key : Symbol (gensym 'IntList_))

(: rassoc (∀ (X) (X X → X) → X * → X))
;; Wraps a binary function so that arguments are processed
;; in a right-associative manner.
(define ((rassoc fn) . args)
  (match-define-values (args* (list argn)) (split-at-right args 1))
  (foldr fn argn args*))

(: lassoc (∀ (X) (X X → X) → X X * → X))
;; Wraps a binary function so that arguments are processed
;; in a left-associative manner. Note that foldl calls functions
;; in their reverse order, so we flip the arguments to fix that.
(define ((lassoc fn) fst . rst)
  (: flip : (X X → X) → X X → X)
  (define ((flip f) x y) (f y x))
  (foldl (flip fn) fst rst))

;; Builtin symbols
(define-builtin-symbol true mk-true)
(define-builtin-symbol false mk-false)
(define-builtin-proc = mk-eq 2)
(define-builtin-proc distinct mk-distinct *)
(define-builtin-proc not mk-not 1)
(define-builtin-proc ite mk-ite 3)
(define-builtin-proc iff mk-iff 2)
(define-builtin-proc => mk-implies rassoc)
(define-builtin-proc xor mk-xor lassoc)
;; These functions already accept an arbitrary number of arguments
(define-builtin-proc and mk-and *)
(define-builtin-proc or mk-or *)
(define-builtin-proc + mk-add *)
(define-builtin-proc * mk-mul *)
(define-builtin-proc - mk-sub *)
;; These don't
(define-builtin-proc / mk-div lassoc)
(define-builtin-proc div mk-div lassoc)
(define-builtin-proc mod mk-mod lassoc)
(define-builtin-proc rem mk-rem lassoc)
(define-builtin-proc ^ mk-power 2)
(define-builtin-proc is-int mk-is-int 1)
;; XXX Comparisons are chainable (i.e. (< a b c) == (and (< a b) (< b c)))
(define-builtin-proc < mk-lt 2)
(define-builtin-proc <= mk-le 2)
(define-builtin-proc > mk-gt 2)
(define-builtin-proc >= mk-ge 2)
;; Array operations
(define-builtin-proc select mk-select 2)
(define-builtin-proc store mk-store 3)


;; Built-in sorts
(define-builtin-sort Bool mk-bool-sort)
(define-builtin-sort Int mk-int-sort)
(define-builtin-sort Real mk-real-sort)
;(define-builtin-sort Array (curryn 2 z3:mk-array-sort))

;; Apply
(: @/s : Symbol Expr * → Z3:Ast)
(define (@/s f . xs) (apply (get-fun f) xs))
(provide @/s)

(define-syntax hash-set*
  (syntax-rules ()
    [(_ m) m]
    [(_ m [x y] rst ...) (hash-set* (hash-set m x y) rst ...)]))

(define-syntax-rule (with-vals x->v e ...)
  (match-let ([(Z3-Ctx ctx solver vals funs sorts) (current-context-info)])
    (define vals*
      (for/fold ([vals* : (HashTable Symbol Z3:Ast) vals])
                ([(x v) x->v])
        (hash-set vals* x v)))
    (smt:with-context (Z3-Ctx ctx solver vals* funs sorts)
      e ...)))

(define-syntax (quant/s stx)
  (syntax-parse stx
    [(_ _ () e) #'e]
    [(_ mk-quant:id ([x:id t] ...) e #:patterns pats)
     #'(let ([cur-ctx (ctx)])
         (let ([x (mk-fresh-const cur-ctx
                                  (symbol->string 'x)
                                  (assert (smt:internal:sort-expr->_z3-sort 't) z3-sort?))] ...)
           (define new-vals
             (for/hasheq : (HashTable Symbol Z3:Ast) ([xᵢ (in-list '(x ...))]
                                                      [cᵢ (in-list (list x ...))])
               (values xᵢ (app-to-ast cur-ctx cᵢ))))
           (define-values (body patterns)
             (with-vals new-vals
               (values (expr->_z3-ast e) pats)))
           (mk-quant cur-ctx 0 (list x ...) patterns body)))]))

(define-simple-macro
  (forall/s ([x:id t] ...) e (~optional (~seq #:patterns pats) #:defaults ([pats #'null])))
  (quant/s mk-forall-const ([x t] ...) e #:patterns pats))
(define-simple-macro
  (exists/s ([x:id t] ...) e (~optional (~seq #:patterns pats) #:defaults ([pats #'null])))
  (quant/s mk-exists-const ([x t] ...) e #:patterns pats))

(define-simple-macro (dynamic-quant/s mk-quant-const xs* ts e #:patterns pats)
  (match xs*
    ['() e]
    [xs
     (define cur-ctx (ctx))
     (define bounds
       (for/list : (Listof Z3:App) ([x xs] [t ts])
         (mk-fresh-const cur-ctx
                         (symbol->string x)
                         (assert (smt:internal:sort-expr->_z3-sort t) z3-sort?))))
     (define new-vals
       (for/hasheq : (HashTable Symbol Z3:Ast) ([x xs] [c bounds])
         (values x (app-to-ast cur-ctx c))))
     (define-values (body patterns)
       (with-vals new-vals
         (values (expr->_z3-ast e) pats)))
     (mk-quant-const cur-ctx 0 bounds patterns body)]))

(define-simple-macro
  (dynamic-forall/s xs ts e (~optional (~seq #:patterns pats) #:defaults ([pats #'null])))
  (dynamic-quant/s mk-forall-const xs ts e #:patterns pats))
(define-simple-macro
  (dynamic-exists/s xs ts e (~optional (~seq #:patterns pats) #:defaults ([pats #'null])))
  (dynamic-quant/s mk-exists-const xs ts e #:patterns pats))

(provide forall/s (rename-out [forall/s ∀/s])
         exists/s (rename-out [exists/s ∃/s])
         dynamic-forall/s (rename-out [dynamic-forall/s dynamic-∀/s])
         dynamic-exists/s (rename-out [dynamic-exists/s dynamic-∃/s]))
