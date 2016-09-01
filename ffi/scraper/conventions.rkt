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

(: api-typ->rkt : String → (Values Symbol Symbol))
;; Convert type in `def-API` line to FFI name, predicate, and TR name
;; This should be consistent with `c-opq->rkt`
(define (api-typ->rkt s)
  (case s
    [("UINT") (values '_uint 'Nonnegative-Fixnum)]
    [("UINT64") (values '_uint64 'Nonnegative-Fixnum)]
    [("VOID") (values '_void 'Void)]
    [("BOOL") (values '_bool 'Boolean)]
    [("STRING") (values '_string 'String)]
    [("DOUBLE") (values '_double 'Flonum)]
    [("FLOAT") (values '_float 'Single-Flonum)]
    [("INT") (values '_int 'Fixnum)]
    [("INT64") (values '_int64 'Fixnum)]
    [("PRINT_MODE")
     ;; TODO stupid doc
     (values '_z3-ast-print-mode 'Z3:Ast-Print-Mode)]
    [else
     (values
      (string->symbol (format "_z3-~a" (string-replace (string-downcase s) "_" "-")))
      (string->symbol (format "Z3:~a" (string-replace (string-titlecase s) "_" "-"))))]))

(: c-variant->rkt : String → String)
;; Convert C enum variant name to Racket symbol name
(define c-variant->rkt
  (match-lambda
    [(regexp #rx"^Z3_(.+)$" (list _ (? string? s)))
     (string-replace (string-downcase s) "_" "-")]))

(: c-fun->rkt ([String] [#:type (U 'pred 'bang #f)] . ->* . String))
;; Convert C name to Racket name
(define (c-fun->rkt x #:type [type #f])
  (match x
    [(regexp #rx"^Z3_(.+)$" (list _ (? string? s)))
     (c-val->rkt s #:type type)]))

(: c-val->rkt ([String] [#:type (U 'pred 'bang #f)] . ->* . String))
(define (c-val->rkt s #:type [type #f])
  (define base-pats
    '([#rx"_to_" "->"]
      [#rx"_" "-"]))
  (define pats
    (case type
      [(pred) (cons '[#rx"^is_(.+)$" "\\1?"] base-pats)]
      [(bang) (cons '[#rx"^(.+)$" "\\1!"] base-pats)]
      [(#f)   base-pats]))
  (assert (regexp-replaces s pats) string?))

