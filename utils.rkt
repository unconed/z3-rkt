#lang racket/base

(require (for-syntax racket/base
                     racket/syntax
                     racket/contract
                     syntax/parse)
         racket/contract
         racket/match
         syntax/parse/define
         (only-in ffi/unsafe cpointer?))

(provide (struct-out z3ctx)
         current-context-info
         ctx
         (struct-out datatype-instance)
         (struct-out z3-complex-sort)
         get-sort
         new-sort!
         set-value!
         get-value
         get-current-model
         set-current-model!
         get-or-create-instance
         )

(define todo/c any/c)
(provide todo/c)

;; Z3 context info structure.
(define-struct/contract z3ctx ([context cpointer?]
                               [vals  (hash/c symbol? todo/c)]
                               [sorts (hash/c symbol? todo/c)]
                               [current-model (box/c (or/c #f todo/c))])
  #:transparent)

; This must be parameterized every time any syntax is used
(define/contract current-context-info (parameter/c z3ctx?) (make-parameter #f))

(define/contract (ctx) (-> cpointer?) (z3ctx-context (current-context-info)))

;; A symbol table for sorts
(define/contract (get-sort id)
  (symbol? . -> . (or/c #f todo/c))
  (hash-ref (z3ctx-sorts (current-context-info)) id #f))
(define (new-sort! id v)
  (symbol? todo/c . -> . void?)
  (define sorts (z3ctx-sorts (current-context-info)))
  (cond [(hash-has-key? sorts id)
         (error 'new-sort! "Defining a pre-existing sort: ~a" id)]
        [else (hash-set! sorts id v)]))

(define (set-value! id v)
  (hash-ref! (z3ctx-vals (current-context-info)) id v))
(define (get-value id)
  (hash-ref (z3ctx-vals (current-context-info)) id))

;; The current model for this context. This is a mutable box.
(define (get-current-model)
  (cond
    [(unbox (z3ctx-current-model (current-context-info))) => values]
    [else (error 'get-current-model "No model found")]))
(define (set-current-model! new-model)
  (set-box! (z3ctx-current-model (current-context-info)) new-model))

;; Indicates an instance of a datatype (e.g. (List Int) for List).
(define-struct/contract datatype-instance ([z3-sort todo/c]
                                           [fns (hash/c symbol? todo/c)])
  #:transparent)

;; A complex sort (e.g. List) has data about the base sort, a creator function
;; (which takes the base sort and a list of sort parameters to apply and produces
;; an immutable datatype-instance. We also want to cache instances for specific sort
;; parameters (so (List Int) followed by (List Int) should return the same
;; datatype-instance.
(define-struct/contract z3-complex-sort ([base-sort todo/c]
                                         [creator (todo/c (listof todo/c) . -> . datatype-instance?)]
                                         [instance-hash (hash/c (listof todo/c) datatype-instance?)])
  #:transparent)

;; Given a base sort and parameter sorts, get or create a parameterized
;; datatype.
(define/contract (get-or-create-instance sort params)
  (todo/c (listof todo/c) . -> . datatype-instance?)
  
  (match-define (z3-complex-sort base creator cache) sort)
  (hash-ref! cache params (λ () (creator base params))))
