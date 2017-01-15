#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/string
         racket/bool)

(: c-typ->rkt : String → (Values String String))
;; Convert C type name to FFI type name and predicate name
(define c-typ->rkt
  (match-lambda
    [(regexp #rx"^Z3_(.+)$" (list _ (? string? s₀)))
     (define s (string-replace s₀ "_" "-"))
     (values (format "_z3-~a" s) (format "z3-~a?" s))]
    [t
     (case t
       [("int") (values "_int" "fixnum?")]
       [("bool") (values "_bool" "boolean?")]
       [("string") (values "_string" "string?")]
       [else (error 'c-typ->rkt "unhandled: ~a" t)])]))

(: api-typ->rkt : String → Symbol)
;; Convert type in `def-API` line to FFI name
;; This should be consistent with `c-opq->rkt`
(define (api-typ->rkt s)
  (case s
    [("UINT") '_uint]
    [("UINT64") '_uint64]
    [("VOID") '_void]
    [("BOOL") '_bool]
    [("STRING") '_string]
    [("DOUBLE") '_double]
    [("FLOAT") '_float]
    [("INT") '_int]
    [("INT64") '_int64]
    [("PRINT_MODE") #|stupid doc|# '_z3-ast-print-mode]
    [else
     (string->symbol (format "_z3-~a" (string-replace (string-downcase s) "_" "-")))]))

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
    '([#px"^(.+)_to_(.+)$" "\\1->\\2"]
      [#rx"_" "-"]))
  (define pats
    (case type
      [(pred) (list* '[#rx"^is_(.+)$" "\\1?"] '[#rx"^(.+)_is_(.+)" "\\1-is-\\2?"] base-pats)]
      [(bang) (cons '[#rx"^(.+)$" "\\1!"] base-pats)]
      [(#f)   base-pats]))
  (assert (regexp-replaces s pats) string?))
