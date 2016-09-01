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

    (define (->id x) (format-id src "~a" x))

    (define/contract ffi->trkt
      (syntax? . -> . syntax?)
      (syntax-parser
        #:literals (_list _fun length)
        ;; Functions
        [(_fun tₓ:id ... (~literal ->) tₐ:id)
         (with-syntax ([(Tₓ ...)
                        (datum->syntax src (map ffi->trkt (syntax->list #'(tₓ ...))))]
                       [Tₐ (ffi->trkt #'tₐ)])
           #'(Tₓ ... → Tₐ))]
        [(_fun (x₀:id ... . xₙ:id) (~literal ::)
               (z₀:id (~literal :) t₀:id) ...
               (_ (~literal :) _uint = (length lₙ:id))
               (zₙ:id (~literal :) (_list (~literal i) tₙ:id))
               (~literal ->)
               tₐ:id)
         #:when (and (free-identifier=? #'xₙ #'lₙ)
                     (free-identifier=? #'xₙ #'zₙ)
                     (andmap free-identifier=?
                             (syntax->list #'(x₀ ...))
                             (syntax->list #'(z₀ ...))))
         (with-syntax ([(T₀ ...)
                        (datum->syntax src (map ffi->trkt (syntax->list #'(t₀ ...))))]
                       [Tₙ (ffi->trkt #'tₙ)]
                       [Tₐ (ffi->trkt #'tₐ)])
           #'(T₀ ... Tₙ * → Tₐ))]
        ;; List
        [(_list (~literal i) t)
         (with-syntax ([T (ffi->trkt #'t)])
           #'(Listof T))]
        ;; Simple
        [(~or (~literal _int) (~literal _int32) (~literal _int64)) #'Fixnum]
        [(~or (~literal _uint) (~literal _uint32) (~literal _uint64)) #'Nonnegative-Fixnum]
        [(~literal _double) #'Flonum]
        [(~literal _float) #'Single-Flonum]
        [(~literal _bool) #'Boolean]
        [_t:id
         (match (symbol->string (syntax-e #'_t))
           [(regexp #rx"^_(.+)$" (list _ (? string? s)))
            (->id (string-titlecase s))]
           [_
            (error 'ffi->trkt "don't know how to convert ~a" (syntax-e #'_t))])]
        [_t
         (printf "Convert ~a to Any for now~n" (syntax->datum #'_t))
         #'Any]))

    (define/contract declare-opaques (listof syntax?)
      (for/list ([dec opaques])
        (match-define (cons _t t?) dec)
        (with-syntax ([T (ffi->trkt (->id _t))]
                      [t? (->id t?)])
          #'[#:opaque T t?])))

    (define/contract declare-enums (listof syntax?)
      (for/list ([(t vs) (in-hash enums)])
        (with-syntax ([t (ffi->trkt (->id t))]
                      [(v ...) (datum->syntax src (for/list ([v vs]) #`(quote #,v)))])
          #'(define-type t (U v ...)))))

    (define/contract declare-bindings (listof syntax?)
      (for/list ([(x t) (in-hash sigs)])
        (with-syntax* ([x (->id x)]
                       [T (ffi->trkt (datum->syntax src t))])
          #'[x T])))
    
    (let ([stx #`(begin
                   (provide #,@(map (compose ffi->trkt ->id) (hash-keys enums)))
                   #,@declare-enums
                   (require/typed/provide "ffi.rkt"
                     #,@declare-opaques
                     #,@declare-bindings))])
      (parameterize ([pretty-print-columns 120])
        (printf "Generated typed module:~n")
        (pretty-write (syntax->datum stx)))
      stx)))

(splicing-let-syntax ([do-it! (λ (stx) (gen stx))])
  (do-it!))
