#lang racket/base

(require (for-syntax racket/base
                     racket/syntax)
         racket/contract
         racket/match
         (except-in ffi/unsafe ->))

(provide (struct-out z3ctx)
         current-context-info
         ctx
         (struct-out datatype-instance)
         (struct-out z3-complex-sort)
         get-sort
         new-sort!
         get-or-create-instance
         builtin-vals-eval-at-init
         builtin-vals
         builtin-sorts
         define-builtin-symbol
         define-builtin-proc
         define-builtin-sort
         curryn)

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
         (error 'new-sort! "Defining a pre-existing sort!")]
        [else (hash-set! sorts id v)]))

;; Indicates an instance of a datatype (e.g. (List Int) for List).
(define-struct/contract datatype-instance ([z3-sort todo/c]
                                           [fns (hash/c todo/c todo/c)])
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

;; Curry a function application exactly n times.
;; (curryn 0 f a b) is the same as (f a b).
;; ((curryn 1 f a b) c d) is the same as (f a b c d) and so on.
(define (curryn n fn . args)
  (if (zero? n)
      (apply fn args)
      (λ more-args (apply curryn (sub1 n) fn (append args more-args)))))

;; This is the prototype namespace for new contexts. It is added to by
;; define-builtin-symbol and define-builtin-proc below.
(define/contract builtin-vals-eval-at-init (hash/c symbol? todo/c) (make-hasheq))
(define/contract builtin-vals              (hash/c symbol? todo/c) (make-hasheq))
(define/contract builtin-sorts             (hash/c symbol? todo/c) (make-hasheq))

(begin-for-syntax
  
  (define (add-smt-suffix stx)
    (format-id stx "~a/s" (syntax->datum stx)))
  
  (define (with-syntax-define-proc name-stx fn-stx)
    (with-syntax ([proc-stx (add-smt-suffix name-stx)]
                  [name name-stx]
                  [fn fn-stx])
      #'(begin
          (define (proc-stx . args) `(@app ,fn ,@args))
          (hash-set! builtin-vals 'name fn)
          (provide proc-stx)))))

(define-syntax (define-builtin-symbol stx)
  (syntax-case stx ()
    [(_ name fn)
     (with-syntax ([proc-stx (add-smt-suffix #'name)])
       #'(begin
           (define proc-stx 'name)
           (hash-set! builtin-vals-eval-at-init 'name fn)
           (provide proc-stx)))]))

(define-syntax (define-builtin-proc stx)
  (syntax-case stx ()
    [(_ name fn)
     (with-syntax-define-proc #'name #'fn)]
    [(_ name fn wrap)
     (with-syntax-define-proc #'name
                              #'(λ (context . args) (apply (wrap (curryn 1 fn context)) args)))]))

(define-syntax-rule (define-builtin-sort name fn)
  (hash-set! builtin-sorts 'name fn))
