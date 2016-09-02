#lang typed/racket/base

(require (for-syntax racket/base
                     racket/set
                     racket/list
                     racket/match
                     racket/syntax
                     syntax/parse
                     racket/contract
                     racket/pretty
                     racket/function)
         ffi/unsafe
         racket/splicing
         "ffi.rkt")

(begin-for-syntax
  
  (define (gen src)

    (define/contract ->rkt-name ((or/c string? symbol?) . -> . string?)
      (match-lambda
        [(? symbol? s) (->rkt-name (symbol->string s))]
        [(regexp #rx"^_(.+)$" (list _ (? string? s)))
         (string-titlecase s)]))

    (define/contract declare-opaques (listof syntax?)
      (for/list ([dec opaques])
        (match-define (cons _t t?) dec)
        (with-syntax ([T (format-id src "~a" (->rkt-name _t))]
                      [t? (format-id src "~a" t?)])
          #'[#:opaque T t?])))

    (define/contract declare-enums (listof syntax?)
      (for/list ([(t vs) (in-hash enums)])
        (with-syntax ([t (format-id src "~a" (->rkt-name t))]
                      [(v ...) (datum->syntax src (for/list ([v vs]) #`(quote #,v)))])
          #'(define-type t (U v ...)))))

    (let ([_ (log-info "Generating Typed Racket type definitions...~n")]
          [stx #`(begin
                   (provide #,@(map (compose (curry format-id src "~a") ->rkt-name)
                                    (hash-keys enums)))
                   #,@declare-enums
                   (require/typed/provide "ffi.rkt"
                     #,@declare-opaques
                     [#:opaque Z3-Null z3-null?]
                     [z3-null Z3-Null]))])
      (parameterize ([pretty-print-columns 120])
          (printf "Generated typed module:~n")
          (pretty-write (syntax->datum stx)))
      (log-info "Finished generating Typed Racket type definitions~n")
      stx)))

(splicing-let-syntax ([do-it! (λ (stx) (gen stx))])
  (do-it!))
