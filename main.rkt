#lang typed/racket/base

(require "z3-wrapper.rkt"
         "parser.rkt"
         "builtins.rkt"
         "derived.rkt")

(require/typed racket/base
  [(make-keyword-procedure
    make-new-context-keyword-procedure)
   (((Listof Keyword) (Listof (U Boolean Integer String)) → Z3-Ctx) →
    ([]
     [#:proof? Boolean
      #:debug-ref-count? Boolean
      #:trace? Boolean
      #:trace-file-name String
      #:timeout Nonnegative-Fixnum
      #:rlimit Nonnegative-Fixnum
      #:type-check? Boolean
      #:well-sorted-check? Boolean
      #:auto-config? Boolean
      #:model? Boolean
      #:model-validate? Boolean
      #:unsat-core? Boolean]
     . ->* . Z3-Ctx))]
  [raise-arity-error (Symbol Natural Any * → Nothing)])

(define z3-default-overrides : (HashTable Keyword (U Boolean Integer String))
  (hasheq '#:timeout 2000
          '#:well-sorted-check? #t))

(: new-context-proc : (Listof Keyword) (Listof (U Boolean Integer String)) → Z3-Ctx)
(define (new-context-proc kws kw-args)
  (define config (mk-config))
  (define params
    (for/fold ([params : (HashTable Keyword (U Boolean Integer String)) z3-default-overrides])
              ([kw kws] [kw-arg kw-args])
      (hash-set params kw kw-arg)))
  (for ([(kw kw-arg) (in-hash params)])
    (define-values (kw-str kw-arg-str) (keyword-arg->_z3-param kw kw-arg))
    (set-param-value! config kw-str kw-arg-str))

  (define ctx (mk-context config))
  (define solver (mk-solver ctx))
  (define-values (vals funs sorts)
    (let ([bootstrap-z3ctx (z3ctx ctx solver (hasheq) (hasheq) (hasheq))]) ;; TODO hacky
      (smt:with-context bootstrap-z3ctx
        (init-builtins))))
  (z3ctx ctx solver vals funs sorts))

; For a list of keyword arguments smt:new-context accepts, see
; http://research.microsoft.com/en-us/um/redmond/projects/z3/config.html.
; All keywords are in standard Racket form, with the words lowercased, the
; underscores changed to hyphens, and a ? suffixed to boolean arguments.
(define smt:new-context (make-new-context-keyword-procedure new-context-proc))

(provide
 (all-from-out "parser.rkt"
               "builtins.rkt"
               "derived.rkt")
 smt:new-context)
