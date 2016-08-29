#lang typed/racket/base

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse
                     racket/contract)
         racket/list
         racket/match
         (only-in racket/function curry)
         syntax/parse/define
         "../ffi/main.rkt"
         "private.rkt"
         )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Utils (from old `utils.rkt`)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(begin-for-syntax
  
  (define/contract (add-smt-suffix id)
    (identifier? . -> . identifier?)
    (format-id id "~a/s" (syntax->datum id)))
  
  (define-syntax-class arity
    #:description "function arity (natural or *)"
    (pattern (~or n:nat (~literal *) (~literal lassoc) (~literal rassoc)))))

(define-syntax define-builtin-symbol
  (syntax-parser
    [(_ x:id v:id)
     (with-syntax ([x/c (add-smt-suffix #'x)])
       #'(begin
           (define-syntax x/c
             (syntax-parser
               [c #:when (identifier? #'c) #'(v (get-context))]))
           (provide x/c)))]))

(define-syntax define-builtin-sort-proc
  (syntax-parser
    [(_ f:id v:id n:nat)
     (with-syntax ([f/c (add-smt-suffix #'f)]
                   [(x ...)
                    (datum->syntax
                     #f
                     (for/list ([i (syntax-e #'n)])
                       (format-id #f "x~a" i)))])
       #'(begin
           (define (f/c [x : Sort-Expr] ...)
             (v (get-context) (sort-expr->_z3-sort x) ...))
           (provide f/c)))]))

(define-syntax (define-builtin-proc stx)
  (syntax-parse stx
    [(_ f:id v n:arity)
     (with-syntax ([f/s (add-smt-suffix #'f)])
       (syntax-parse #'n
         [k:nat
          (with-syntax ([(x ...)
                         (datum->syntax
                          #f
                          (for/list ([i (syntax-e #'k)])
                            (format-id #f "x~a" i)))])
            #'(begin
                (define (f/s [x : Expr] ...)
                  #;(printf "Applying ~a to ~a~n"
                          'f/s
                          (list `(,(ast-to-string (get-context) (expr->_z3-ast x)) :
                                  ,(sort-to-string (get-context) (z3-get-sort (get-context) (expr->_z3-ast x)))) ...))
                  (v (get-context) (expr->_z3-ast x) ...))
                (provide f/s)))]
         [(~literal *)
          #'(begin
              (define (f/s . [xs : Expr *])
                (define args (map expr->_z3-ast xs))
                #;(printf "Applying ~a to ~a~n"
                          'f/s
                          (for/list : (Listof String) ([arg args])
                            (ast-to-string (get-context) arg)))
                (apply v (get-context) (map expr->_z3-ast xs)))
              (provide f/s))]
         [(~literal lassoc)
          #'(begin
              (define f/s (lassoc (λ (x y) (v (get-context) x y))))
              (provide f/s))]
         [(~literal rassoc)
          #'(begin
              (define f/s (rassoc (λ (x y) (v (get-context) x y))))
              (provide f/s))]))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; from old `builtins.rkt`
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: rassoc : (Z3:Ast Z3:Ast → Z3:Ast) → Expr Expr * → Z3:Ast)
;; Wraps a binary function so that arguments are processed
;; in a right-associative manner.
(define ((rassoc fn) . args)
  (let loop ([args : (Listof Expr) args])
    (match args
      [(list arg) (expr->_z3-ast arg)]
      [(cons arg args*)
       (fn (expr->_z3-ast arg) (loop args*))])))

(: lassoc : (Z3:Ast Z3:Ast → Z3:Ast) → Expr Expr * → Z3:Ast)
;; Wraps a binary function so that arguments are processed in a left-associative manner.
(define ((lassoc fn) fst . rst)
  (for/fold ([acc : Z3:Ast (expr->_z3-ast fst)]) ([x rst])
    (fn acc (expr->_z3-ast x))))

;; Builtin constants
(define-builtin-symbol true mk-true)
(define-builtin-symbol false mk-false)

;; Builtin sorts
(define-builtin-symbol Int mk-int-sort)
(define-builtin-symbol Real mk-real-sort)
(define-builtin-symbol Bool mk-bool-sort)
(define-builtin-sort-proc Array mk-array-sort 2)
(define-builtin-sort-proc Set mk-set-sort 1)

;; Builtin symbols
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
(define-builtin-proc to-real mk-int2real 1)
;; XXX Comparisons are chainable (i.e. (< a b c) == (and (< a b) (< b c)))
(define-builtin-proc < mk-lt 2)
(define-builtin-proc <= mk-le 2)
(define-builtin-proc > mk-gt 2)
(define-builtin-proc >= mk-ge 2)

;; Arrays
(define-builtin-proc select mk-select 2)
(define-builtin-proc store mk-store 3)

;; Sets
(define-builtin-sort-proc empty mk-empty-set 1)
(define-builtin-sort-proc full mk-full-set 1)
(define-builtin-proc add mk-set-add 2)
(define-builtin-proc del mk-set-del 2)
(define-builtin-proc union mk-set-union *)
(define-builtin-proc intersect mk-set-intersect *)
(define-builtin-proc difference mk-set-difference 2)
(define-builtin-proc complement mk-set-complement 1)
(define-builtin-proc member mk-set-member 2)
(define-builtin-proc subset mk-set-subset 2)

;; Apply
(: @/s : Symbol Expr * → Z3:Ast)
(define (@/s f . xs)
  #;(printf "@/s ~a ~a~n"
          f
          (for/list : (Listof Any) ([x xs])
            (ast-to-string (get-context) (expr->_z3-ast x))))
  (apply (get-fun f) xs))
(provide @/s)

(define-syntax hash-set*
  (syntax-rules ()
    [(_ m) m]
    [(_ m [x y] rst ...) (hash-set* (hash-set m x y) rst ...)]))

(define-syntax (quant/s stx)
  (syntax-parse stx
    [(_ _ () e) #'e]
    [(_ mk-quant:id ([x:id t] ...) e #:pattern pats)
     #'(let ([ctx (get-context)])
         (let ([x (mk-const ctx
                            (make-symbol 'x)
                            (assert (sort-expr->_z3-sort t) z3-sort?))] ...)
           (define new-vals
             (for/hasheq : (HashTable Symbol Z3:Ast) ([xᵢ (in-list '(x ...))]
                                                      [cᵢ (in-list (list x ...))])
               (values xᵢ (app-to-ast ctx cᵢ))))
           (define-values (body patterns)
             (with-extended-vals new-vals
               (values (expr->_z3-ast e) pats)))
           (mk-quant ctx 0 (list x ...) patterns body)))]))

(define-simple-macro
  (forall/s ([x:id t] ...) e (~optional (~seq #:pattern pats) #:defaults ([pats #'null])))
  (quant/s mk-forall-const ([x t] ...) e #:pattern pats))
(define-simple-macro
  (exists/s ([x:id t] ...) e (~optional (~seq #:pattern pats) #:defaults ([pats #'null])))
  (quant/s mk-exists-const ([x t] ...) e #:pattern pats))

(define-simple-macro (dynamic-quant/s mk-quant-const xs* ts e #:pattern pats)
  (match xs*
    ['() e]
    [xs
     (define ctx (get-context))
     (define bounds
       (for/list : (Listof Z3:App) ([x xs] [t ts])
         (mk-const ctx (make-symbol x) (assert (sort-expr->_z3-sort t) z3-sort?))))
     (define new-vals
       (for/hasheq : (HashTable Symbol Z3:Ast) ([x xs] [c bounds])
         (values x (app-to-ast ctx c))))
     (define-values (body patterns)
       (with-extended-vals new-vals
         (values (expr->_z3-ast e) pats)))
     (mk-quant-const ctx 0 bounds patterns body)]))

(define-simple-macro
  (dynamic-forall/s xs ts e (~optional (~seq #:pattern pats) #:defaults ([pats #'null])))
  (dynamic-quant/s mk-forall-const xs ts e #:pattern pats))
(define-simple-macro
  (dynamic-exists/s xs ts e (~optional (~seq #:pattern pats) #:defaults ([pats #'null])))
  (dynamic-quant/s mk-exists-const xs ts e #:pattern pats))

(provide forall/s (rename-out [forall/s ∀/s])
         exists/s (rename-out [exists/s ∃/s])
         dynamic-forall/s (rename-out [dynamic-forall/s dynamic-∀/s])
         dynamic-exists/s (rename-out [dynamic-exists/s dynamic-∃/s]))
