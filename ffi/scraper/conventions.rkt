#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/string)

(: c-opq->rkt : String → (Values String String String))
;; Convert C opaque pointer name to FFI type name, predicate, and TR name
(define c-opq->rkt
  (match-lambda
    [(regexp #rx"^Z3_(.+)$" (list _ (? string? s₀)))
     (define s (string-replace s₀ "_" "-"))
     (values (format "_z3-~a" s)
             (format "z3-~a?" s)
             (format "Z3:~a" (string-titlecase s)))]))

(: c-variant->rkt : String → String)
;; Convert C enum variant name to Racket symbol name
(define c-variant->rkt
  (match-lambda
    [(regexp #rx"^Z3_(.+)$" (list _ (? string? s)))
     (string-replace (string-downcase s) "_" "-")]))

(: c-fun->rkt : String → String)
;; Convert C name to Racket name
(define c-fun->rkt
  (match-lambda
    [(regexp #rx"^Z3_(.+)$" (list _ (? string? s)))
     (assert (regexp-replaces s '((#rx"_to_" "->")
                                  (#rx"_" "-")))
             string?)]))
