#lang racket/base

(require (for-syntax racket/base
                     racket/match
                     racket/list
                     racket/set
                     racket/syntax
                     syntax/parse
                     racket/contract
                     racket/function
                     racket/pretty
                     "scrape.rkt"
                     "conventions.rkt")
         ffi/unsafe
         racket/string
         racket/match)

#|
* Untyped FFI:
  - convert type name -> ffi-name
  - convert def-api value name -> ffi-name
  - declare tagged cpointers for opaque types
  - define enums for enums
  - for each entry in def-api:
    + multiple out params -> racket multiple returns
    + arrays with length -> racket tuple
      * 1  -> values
      * 2  -> cons
      * 3+ -> list
    + 1 out-param with success flag -> optional (assume no overlap with boolean)
    + 1 length and 1 array -> varargs
    + void with no out -> suffix `!`
    + boolean with no out -> suffix `?`
    + standard renamings: "_" -> "-", "_to_" -> "->", no "Z3_" prefix
|#

(begin-for-syntax

  (define (gen src)

    (define-values (def-api-ret def-api-arg sig-ret sig-arg opaques enums)
      (scrape (open-input-file "Z3-api/Z3_ C API.html")))

    (define-values (provides-add! provides)
      (let ()
        (define/contract ps (listof identifier?) '())
        (values
         (λ (x) (set! ps (cons x ps)))
         (λ () (reverse ps)))))

    ;; Generate FFI and TR names for opaque types
    (define-values (_ts t?s Ts)
      (for/lists (_ts t?s Ts) ([x opaques])
        (c-opq->rkt x)))

    (define/contract define-opaque-cpointers (listof syntax?)
      (let ()
        (for ([t? (in-list t?s)])
          (provides-add! (format-id src "~a" t?)))
        (for/list ([_t (in-list _ts)])
          (with-syntax ([_t (format-id src "~a" _t)])
            #'(define-cpointer-type _t)))))

    (define/contract define-enums (listof syntax?)
      (let ()
        (for/list ([(t vs) (in-hash enums)])
          (define-values (_t t? _) (c-opq->rkt t))
          (define/contract vars list?
            (for/list ([v vs])
              (match v
                [(? string? s)
                 (string->symbol (c-variant->rkt s))]
                [(cons s i)
                 (define l (string->symbol (c-variant->rkt s)))
                 `(,l = ,i)])))
          (define vars-adjusted
            (append-map (match-lambda
                          [(? list? l) l]
                          [x (list x)])
                        vars))
          ;(provides-add! (format-id src "~a" t?))
          (with-syntax ([_t (format-id src "~a" _t)])
            #`(define _t (_enum '#,vars-adjusted _int32))))))

    (define stx
      #`(begin
          #,@define-opaque-cpointers
          #,@define-enums
          (provide #,@(provides))))
    (printf "Gen:~n")
    (pretty-write (syntax->datum stx))
    stx))

(define-syntax (do-it stx) (gen stx))

(do-it)
