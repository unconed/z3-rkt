#lang racket/base

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse
                     racket/contract)
         racket/list
         racket/match
         racket/contract
         syntax/parse/define
         "utils.rkt"
         "parser.rkt"
         (prefix-in z3: "z3-wrapper.rkt"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Utils (from old `utils.rkt`)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This is the prototype namespace for new contexts. It is added to by
;; define-builtin-symbol and define-builtin-proc below.
(define/contract builtin-vals-eval-at-init (hash/c symbol? todo/c) (make-hasheq))
(define/contract builtin-sorts             (hash/c symbol? todo/c) (make-hasheq))

(begin-for-syntax
  
  (define/contract (add-smt-suffix id)
    (identifier? . -> . identifier?)
    (format-id id "~a/s" (syntax->datum id)))
  
  (define/contract (with-syntax-define-proc f v)
    (identifier? syntax? . -> . syntax?)
    (with-syntax ([f/s (add-smt-suffix f)])
      #`(begin
          (define (f/s . args) (apply #,v (ctx) (map z3:expr->_z3-ast args)))
          (provide f/s)))))

(define-syntax (define-builtin-symbol stx)
  (syntax-parse stx
    [(_ c:id v)
     (with-syntax ([c/s (add-smt-suffix #'c)])
       #'(begin
           (define c/s 'c) ; PN: why not assign `v` to it? There's always `ctx` that needs passing in
           (hash-set! builtin-vals-eval-at-init 'c v)
           (provide c/s)))]))

(define-syntax (define-builtin-proc stx)
  (syntax-parse stx
    [(_ f:id v)
     (with-syntax-define-proc #'f #'v)]
    [(_ f:id v wrap)
     (with-syntax-define-proc
       #'f
       #'(λ (ctx . args) (apply (wrap (curryn 1 v ctx)) args)))]))

(define-simple-macro (define-builtin-sort x:id v)
  (hash-set! builtin-sorts 'x v))

;; Curry a function application exactly n times.
;; (curryn 0 f a b) is the same as (f a b).
;; ((curryn 1 f a b) c d) is the same as (f a b c d) and so on.
(define (curryn n fn . args)
  (if (zero? n)
      (apply fn args)
      (λ more-args (apply curryn (sub1 n) fn (append args more-args)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; from old `builtins.rkt`
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Initialize builtins. (The current context is assumed to be a parameter.)
(define (init-builtins!)
  (match-define (z3ctx ctx vals sorts _) (current-context-info))
  (for ([(k fn) (in-hash builtin-sorts)])
    (new-sort! k (fn ctx)))
  ;; XXX This is a giant hack and needs to be generalized.
  (define int-list-instance
    (z3:mk-list-sort ctx (smt:internal:make-symbol 'IntList) (get-sort 'Int)))
  (new-sort! 'IntList (datatype-instance-z3-sort int-list-instance))
  (hash-set! vals int-list-key int-list-instance)

  (for ([(k fn) (in-hash builtin-vals-eval-at-init)])
    (hash-set! vals k (fn ctx))))
(provide init-builtins!)

(define int-list-key (gensym 'IntList_))
;; XXX This is a giant hack and needs to be generalized.
(define ((get-list-op op) _context . args)
  (match-define (z3ctx ctx vals _ _) (current-context-info))
  (define instance-fns (datatype-instance-fns (hash-ref vals int-list-key)))
  (define func-decl (hash-ref instance-fns op))
  ;; Make an app out of it. (Drop the first argument since it'll be the context.)
  (apply z3:mk-app ctx func-decl args))

;; Wraps a binary function so that arguments are processed
;; in a right-associative manner.
(define ((rassoc fn) . args)
  (match-define-values (args* (list argn)) (split-at-right args 1))
  (foldr fn argn args*))

;; Wraps a binary function so that arguments are processed
;; in a left-associative manner. Note that foldl calls functions
;; in their reverse order, so we flip the arguments to fix that.
(define ((lassoc fn) fst . rst)
  (define ((flip f) x y) (f y x))
  (foldl (flip fn) fst rst))

;; Builtin symbols
(define-builtin-symbol true z3:mk-true)
(define-builtin-symbol false z3:mk-false)
(define-builtin-proc = z3:mk-eq)
(define-builtin-proc distinct z3:mk-distinct)
(define-builtin-proc not z3:mk-not)
(define-builtin-proc ite z3:mk-ite)
(define-builtin-proc iff z3:mk-iff)
(define-builtin-proc => z3:mk-implies rassoc)
(define-builtin-proc xor z3:mk-xor lassoc)
;; These functions already accept an arbitrary number of arguments
(define-builtin-proc and z3:mk-and)
(define-builtin-proc or z3:mk-or)
(define-builtin-proc + z3:mk-add)
(define-builtin-proc * z3:mk-mul)
(define-builtin-proc - z3:mk-sub)
;; These don't
(define-builtin-proc / z3:mk-div lassoc)
(define-builtin-proc div z3:mk-div lassoc)
(define-builtin-proc mod z3:mk-mod lassoc)
(define-builtin-proc rem z3:mk-rem lassoc)
(define-builtin-proc is-int z3:mk-is-int)
;; XXX Comparisons are chainable (i.e. (< a b c) == (and (< a b) (< b c)))
(define-builtin-proc < z3:mk-lt)
(define-builtin-proc <= z3:mk-le)
(define-builtin-proc > z3:mk-gt)
(define-builtin-proc >= z3:mk-ge)
;; Array operations
(define-builtin-proc select z3:mk-select)
(define-builtin-proc store z3:mk-store)
;; List operations
(define-builtin-proc insert (get-list-op 'cons))
(define-builtin-proc head (get-list-op 'head))
(define-builtin-proc tail (get-list-op 'tail))
(define-builtin-symbol nil (get-list-op 'nil)) ; This is called so we can use nil/s directly

;; Built-in sorts
(define-builtin-sort Bool z3:mk-bool-sort)
(define-builtin-sort Int z3:mk-int-sort)
(define-builtin-sort Real z3:mk-real-sort)
(define-builtin-sort Array (curryn 2 z3:mk-array-sort))

(define-simple-macro (quant/s mk-quant:id ([x:id t] ...) e)
  (let ([cur-ctx (ctx)])
    (let ([x (z3:mk-fresh-const cur-ctx
                                (symbol->string 'x)
                                (smt:internal:sort-expr->_z3-sort 't))] ...)
      (mk-quant cur-ctx 0 (list x ...) '() (z3:expr->_z3-ast e)))))

(define-simple-macro (forall/s ([x:id t] ...) e)
  (quant/s z3:mk-forall-const ([x t] ...) e))
(define-simple-macro (exists/s ([x:id t] ...) e)
  (quant/s z3:mk-exists-const ([x t] ...) e))

(define/contract ((dynamic-quant mk-quant-const) xs ts e)
  (any/c . -> . ((listof symbol?) (listof any/c) any/c . -> . z3:z3-ast?))
  (define cur-ctx (ctx))
  (define bounds
    (for/list ([x xs] [t ts])
      (z3:mk-fresh-const cur-ctx
                         (symbol->string x)
                         (smt:internal:sort-expr->_z3-sort t))))
  (mk-quant-const cur-ctx 0 bounds '() (z3:expr->_z3-ast e)))

(define dynamic-forall/s (dynamic-quant z3:mk-forall-const))
(define dynamic-exists/s (dynamic-quant z3:mk-exists-const))

(provide forall/s (rename-out [forall/s ∀/s])
         exists/s (rename-out [exists/s ∃/s])
         dynamic-forall/s (rename-out [dynamic-forall/s dynamic-∀/s])
         dynamic-exists/s (rename-out [dynamic-exists/s dynamic-∃/s]))
