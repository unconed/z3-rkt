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
         racket/splicing
         ffi/unsafe
         racket/string
         racket/match)

#|
* Untyped FFI:
  - [x] convert type name -> ffi-name
  - [ ] convert def-api value name -> ffi-name
  - [x] declare tagged cpointers for opaque types
  - [x] define enums for enums
  - for each entry in def-api:
    + [ ] multiple out params -> racket multiple returns
    + [ ] arrays with length -> racket tuple
      * 1  -> values
      * 2  -> cons
      * 3+ -> list
    + [ ] 1 out-param with success flag -> optional (assume no overlap with boolean)
    + [ ] 1 length and 1 array -> varargs
    + [ ] void with no out -> suffix `!`
    + [ ] boolean with no out -> suffix `?`
|#

(begin-for-syntax

  (define (gen src)
    
    (define (->id x) (format-id src "~a" x))
    (define (->stx x) (syntax->datum src x))

    (define-values (api-ret api-arg sig-ret sig-arg opaques enums)
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
          (provides-add! (->id t?)))
        (for/list ([_t (in-list _ts)])
          (with-syntax ([_t (->id _t)])
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
          (with-syntax ([_t (->id _t)])
            #`(define _t (_enum '#,vars-adjusted _int32))))))

    (define/contract define-bindings (listof syntax?)
      (let ()
        (for/list ([(x tₐ) (in-hash api-ret)])
          (define-values (_tₐ Tₐ) (api-typ->rkt tₐ))
          (define tₓ-list (hash-ref api-arg x))
          (with-syntax ([x₀ (datum->syntax src x)]
                        [x (->id (c-fun->rkt x))]
                        [_tₐ (->id _tₐ)]
                        [(_tₓ ...)
                         (for/list ([tₓ (in-list tₓ-list)])
                           (match-define (cons in? t) tₓ)
                           (match t
                             [(cons _ t)
                              (define-values (_t T) (api-typ->rkt t))
                              (with-syntax ([_t (->id _t)])
                                #'(_list i _t))]
                             [t
                              (define-values (_t T) (api-typ->rkt t))
                              (->id _t)]))])
            (provides-add! #'x)
            #'(define x (get-z3 x₀ (_fun _tₓ ... -> _tₐ)))))))

    (define stx
      #`(begin
          #,@define-opaque-cpointers
          #,@define-enums
          #,@define-bindings
          (provide #,@(provides))))
    (printf "Gen:~n")
    (pretty-write (syntax->datum stx))
    stx))

(define libz3
  (let ([lib-name (case (system-type 'os)
                    [(unix) "libz3.so"]
                    [(windows) "z3.dll"]
                    [(macosx) "libz3.dylib"])])
    (define Z3_LIB "Z3_LIB")
    (define libz3-path (getenv Z3_LIB))
    (cond
      [libz3-path
       (define libz3-without-suffix (path-replace-extension (build-path libz3-path lib-name) ""))
       (ffi-lib libz3-without-suffix)]
      [else
       (error 'z3-rkt
              "Cannot locate Z3 libary. Please set ${~a} to the directory containing ~a"
              Z3_LIB
              lib-name)])))

(define (get-z3 x t) (get-ffi-obj x libz3 t))

(splicing-let-syntax ([do-it (λ (stx) (gen stx))])
  (do-it))
