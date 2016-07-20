#lang racket/base

(require racket/list
         racket/match
         syntax/parse/define
         "utils.rkt"
         "parser.rkt"
         (prefix-in z3: "z3-wrapper.rkt"))

;; Initialize builtins. (The current context is assumed to be a parameter.)
(define (init-builtins!)
  (match-define (z3ctx ctx vals sorts _) (current-context-info))
  (for ([(k fn) (in-hash builtin-sorts)])
    (new-sort! k (fn ctx)))
  ;; XXX This is a giant hack and needs to be generalized.
  (define int-list-instance (z3:mk-list-sort ctx (smt:internal:make-symbol 'IntList) (get-sort 'Int)))
  (new-sort! 'IntList (datatype-instance-z3-sort int-list-instance))
  (hash-set! vals int-list-key int-list-instance)

  (for ([(k fn) (in-hash builtin-vals-eval-at-init)])
    (hash-set! vals k (fn ctx)))
  (for ([(k v) (in-hash builtin-vals)])
    (hash-set! vals k v)))
(provide init-builtins!)

(define int-list-key (gensym))
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

(define ((flip f) x y) (f y x))

;; Wraps a binary function so that arguments are processed
;; in a left-associative manner. Note that foldl calls functions
;; in their reverse order, so we flip the arguments to fix that.
(define ((lassoc fn) fst . rst)
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

(define-simple-macro (quant/s q:id ([x:id t] ...) e)
  (let ([x (z3:mk-fresh-const (ctx)
                              (symbol->string 'x)
                              (smt:internal:sort-expr->_z3-sort 't))] ...)
    `(@app q (,x ...) ,e)))

;; forall. The syntax is (forall/s (list of bound variables) expression).
(define-simple-macro (forall/s ([x:id t] ...) e) (quant/s forall ([x t] ...) e))
(define-simple-macro (exists/s ([x:id t] ...) e) (quant/s exists ([x t] ...) e))
(hash-set! builtin-vals 'forall (λ (ctx xs e) (z3:mk-forall-const ctx 0 xs '() e)))
(hash-set! builtin-vals 'exists (λ (ctx xs e) (z3:mk-exists-const ctx 0 xs '() e)))

(provide forall/s
         (rename-out [forall/s ∀/s])
         exists/s
         (rename-out [exists/s ∃/s]))
