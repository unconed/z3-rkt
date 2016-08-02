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
(define builtin-vals-eval-at-init : (HashTable Symbol (Z3:Context → TODO)) (make-hasheq))
(define builtin-sorts             : (HashTable Symbol (Z3:Context → Z3:Sort)) (make-hasheq))

(begin-for-syntax
  
  (define/contract (add-smt-suffix id)
    (identifier? . -> . identifier?)
    (format-id id "~a/s" (syntax->datum id)))
  
  (define/contract (with-syntax-define-proc f v n)
    (identifier? syntax? exact-nonnegative-integer? . -> . syntax?)
    (with-syntax ([f/s (add-smt-suffix f)])
      #`(begin
          (define (f/s . args) (apply #,v (ctx) (map expr->_z3-ast args)))
          (provide f/s))))
  (define-syntax-class arity
    #:description "function arity (natural or *)"
    (pattern (~or n:nat (~literal *)))))

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
    [(_ f:id
        v
        n:arity
        (~optional wrap #:defaults ([(wrap 0) #'values])))
     (with-syntax ([f/s (add-smt-suffix #'f)])
       (syntax-parse #'n
         [k:nat
          (with-syntax ([(x ...)
                         (datum->syntax
                          #f
                          (build-list (syntax->datum #'k)
                                      (λ (i) (format-id #f "x~a" i))))])
            #`(begin
                (define f/s
                  (let ([f-ctx
                         (λ (x ...)
                            (v (ctx) (expr->_z3-ast x) ...))])
                    (wrap f-ctx)))
                (provide f/s)))]
         [(~literal *)
          #`(begin
              (define f/s
                (let ([f-ctx (λ xs (apply v (ctx) (map expr->_z3-ast xs)))])
                  (wrap f-ctx)))
              (provide f/s))]))]))

(define-simple-macro (define-builtin-sort x:id v)
  (hash-set! builtin-sorts 'x v))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; from old `builtins.rkt`
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Initialize builtins. (The current context is assumed to be a parameter.)
(define (init-builtins!)
  (match-define (z3ctx ctx vals funs sorts _) (current-context-info))
  (for ([(k fn) (in-hash builtin-sorts)])
    (new-sort! k (fn ctx)))
  ;; XXX This is a giant hack and needs to be generalized.
  (define int-list-instance
    (mk-list-sort ctx (smt:internal:make-symbol 'IntList) (assert (get-sort 'Int) z3-sort?)))
  (new-sort! 'IntList (datatype-instance-z3-sort int-list-instance))
  (hash-set! vals int-list-key int-list-instance)

  (for ([(k fn) (in-hash builtin-vals-eval-at-init)])
    (hash-set! vals k (fn ctx))))
(provide init-builtins!)

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
(define-builtin-proc => mk-implies 2 rassoc)
(define-builtin-proc xor mk-xor 2 lassoc)
;; These functions already accept an arbitrary number of arguments
(define-builtin-proc and mk-and *)
(define-builtin-proc or mk-or *)
(define-builtin-proc + mk-add *)
(define-builtin-proc * mk-mul *)
(define-builtin-proc - mk-sub *)
;; These don't
(define-builtin-proc / mk-div 2 lassoc)
(define-builtin-proc div mk-div 2 lassoc)
(define-builtin-proc mod mk-mod 2 lassoc)
(define-builtin-proc rem mk-rem 2 lassoc)
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

(define-simple-macro (quant/s mk-quant:id ([x:id t] ...) e)
  (let ([cur-ctx (ctx)])
    (let ([x (mk-fresh-const cur-ctx
                             (symbol->string 'x)
                             (assert (smt:internal:sort-expr->_z3-sort 't) z3-sort?))] ...)
      (mk-quant cur-ctx 0 (list x ...) '() (expr->_z3-ast e)))))

(define-simple-macro (forall/s ([x:id t] ...) e)
  (quant/s mk-forall-const ([x t] ...) e))
(define-simple-macro (exists/s ([x:id t] ...) e)
  (quant/s mk-exists-const ([x t] ...) e))

(: dynamic-quant : (Z3:Context
                    Nonnegative-Fixnum
                    (Listof Z3:App)
                    (Listof Z3:Pattern)
                    Z3:Ast →
                    Z3:Ast) →
   (Listof Symbol) (Listof Any) Any → Z3:Ast)
(define ((dynamic-quant mk-quant-const) xs ts e)
  (define cur-ctx (ctx))
  (define bounds
    (for/list : (Listof Z3:App) ([x xs] [t ts])
      (mk-fresh-const cur-ctx
                      (symbol->string x)
                      (assert (smt:internal:sort-expr->_z3-sort t) z3-sort?))))
  (mk-quant-const cur-ctx 0 bounds '() (expr->_z3-ast e)))

(define dynamic-forall/s (dynamic-quant mk-forall-const))
(define dynamic-exists/s (dynamic-quant mk-exists-const))

(provide forall/s (rename-out [forall/s ∀/s])
         exists/s (rename-out [exists/s ∃/s])
         dynamic-forall/s (rename-out [dynamic-forall/s dynamic-∀/s])
         dynamic-exists/s (rename-out [dynamic-exists/s dynamic-∃/s]))

#|

;; XXX This is a giant hack and needs to be generalized.
(define ((get-list-op op) _context . args)
  (match-define (z3ctx ctx vals _ _) (current-context-info))
  (define instance-fns (datatype-instance-fns (hash-ref vals int-list-key)))
  (define func-decl (hash-ref instance-fns op))
  ;; Make an app out of it. (Drop the first argument since it'll be the context.)
  (apply z3:mk-app ctx func-decl args))

;; List operations
(define-builtin-proc insert (get-list-op 'cons))
(define-builtin-proc head (get-list-op 'head))
(define-builtin-proc tail (get-list-op 'tail))
(define-builtin-symbol nil (get-list-op 'nil)) ; This is called so we can use nil/s directly


|#
