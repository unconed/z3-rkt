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
         "types.rkt"
         (only-in "ffi.rkt" sigs))

(begin-for-syntax
  
  (define (gen src)

    (define (->id x) (format-id src "~a" x))

    (define/contract (figure-out-type x clauses)
      (identifier? (listof syntax?) . -> . syntax?)

      (define/contract (get-matching-type) (-> (or/c #f syntax?))
        (for/or ([clause (in-list clauses)])
          (syntax-parse clause
            [(z:id (~literal :) t _ ...) #:when (free-identifier=? #'z x)
             (ffi->trkt #'t)]
            [_ #f])))

      (define/contract (collect-array-type) (-> (or/c #f syntax?))
        (match (filter values
                       (for/list ([clause (in-list clauses)])
                         (syntax-parse clause
                           [(z:id (~literal :) t (~literal =) ((~literal map) _ l:id))
                            #:when (free-identifier=? #'l x)
                            (syntax-parse (ffi->trkt #'t)
                              [((~literal Listof) T) #'T])]
                           [_ #f])))
          ['()
           (error 'collect-array-type "impossible: 0-sized tuple")]
          [(list T₁ T₂)
           #`(Listof (Pairof #,T₁ #,T₂))]
          [Ts #`(Listof (List #,@Ts))]))
      
      (or (get-matching-type)
          (collect-array-type)))

    (define/contract ffi->trkt
      (syntax? . -> . syntax?)
      (syntax-parser
        #:literals (_list _fun _ptr length)
        ;; Functions
        [(_fun tₓ:id ... (~literal ->) tₐ:id)
         (with-syntax ([(Tₓ ...)
                        (datum->syntax src (map ffi->trkt (syntax->list #'(tₓ ...))))]
                       [Tₐ (ffi->trkt #'tₐ)])
           #'(Tₓ ... → Tₐ))]
        [(_fun (x:id (~literal :) tₓ eₓ ...) ... (~literal ->) res ...)
         (with-syntax ([(z ...)
                        (filter
                         values
                         (for/list ([clause (in-list (syntax->list #'([x tₓ eₓ ...] ...)))])
                           (syntax-parse clause
                             #:literals (_list _ptr)
                             [(_:id ((~or (~literal _list) (~literal _ptr))
                                     (~literal o)
                                     _ ...)
                                    _ ...) #f]
                             [(x:id _ ...) #'x])))])
           (ffi->trkt #'(_fun (z ...) :: (x : tₓ eₓ ...) ... -> res ...)))]
        [(_fun (z:id ...) (~literal ::)
               (x:id (~literal :) tₓ eₓ ...) ...
               (~literal ->)
               res ...)
         (define clauses
           (syntax-parse #'(res ...)
             [(xₐ:id (~literal :) tₐ)
              (cons #'(xₐ : tₐ) (syntax->list #'([x : tₓ eₓ ...] ...)))]
             [_ (syntax->list #'([x : tₓ eₓ ...] ...))]))
         (with-syntax ([(Tₓ ...)
                        (datum->syntax
                         src
                         (for/list ([zᵢ (in-list (syntax->list #'(z ...)))])
                           (figure-out-type zᵢ clauses)))])
           (syntax-parse #'(res ...)
             [(tₐ:id)
              (with-syntax ([Tₐ (ffi->trkt #'tₐ)])
                #'(Tₓ ... → Tₐ))]
             [((res:id (~literal :) tₐ:id) (~literal ->) ans)
              (with-syntax ([Tₐ (ffi->trkt #'tₐ)])
                (syntax-parse #'ans
                  [((~literal and) res rhs)
                   #:when (free-identifier=? #'tₐ #'_bool)
                   (syntax-parse #'rhs
                     [((~literal list) xₐ)
                      (with-syntax ([Tₓₐ (figure-out-type #'xₐ clauses)])
                        #'(Tₓ ... → (Option (List Tₓₐ))))]
                     [xₐ:id
                      (with-syntax ([Tₓₐ (figure-out-type #'xₐ clauses)])
                        #'(Tₓ ... → (Option Tₓₐ)))])]
                  [((~literal values) xₐ₀:id xₐ:id ...)
                   #:when (free-identifier=? #'res #'xₐ₀)
                   (with-syntax ([(Tₓₐ ...)
                                  (datum->syntax
                                   src
                                   (for/list ([x (in-list (syntax->list #'(xₐ ...)))])
                                     (figure-out-type x clauses)))])
                     #'(Tₓ ... → (Values Tₐ Tₓₐ ...)))]
                  [xₐ:id
                   (with-syntax ([Tₓₐ (figure-out-type #'xₐ clauses)])
                     #'(Tₓ ... → Tₓₐ))]))]
             [(tₐ:id (~literal ->) ans)
              (syntax-parse #'ans
                [((~literal values) xₐ:id ...)
                 (with-syntax ([(Tₓₐ ...)
                                (datum->syntax
                                 src
                                 (for/list ([x (in-list (syntax->list #'(xₐ ...)))])
                                   (figure-out-type x clauses)))])
                   #'(Tₓ ... → (Values Tₓₐ ...)))]
                [xₐ:id
                 (with-syntax ([Tₓₐ (figure-out-type #'xₐ clauses)])
                   #'(Tₓ ... → Tₓₐ))])]))]
        ;; List
        [(_list _ t _ ...)
         (with-syntax ([T (ffi->trkt #'t)])
           #'(Listof T))]
        [(_ptr o t) (ffi->trkt #'t)]
        ;; Simple
        [(~or (~literal _int) (~literal _int32) (~literal _int64)) #'Fixnum]
        [(~or (~literal _uint) (~literal _uint32) (~literal _uint64)) #'Nonnegative-Fixnum]
        [(~literal _double) #'Flonum]
        [(~literal _float) #'Single-Flonum]
        [(~literal _bool) #'Boolean]
        [_t:id
         (match (symbol->string (syntax-e #'_t))
           [(regexp #rx"^_(.+)/null$" (list _ (? string? s)))
            (with-syntax ([T (ffi->trkt (format-id src "_~a" s))])
              #'(U Z3-Null T))]
           [(regexp #rx"^_(.+)$" (list _ (? string? s)))
            (->id (string-titlecase s))]
           [_
            (error 'ffi->trkt "don't know how to convert ~a" (syntax-e #'_t))])]
        [_t
         (printf "Convert ~a to Nothing for now~n" (syntax->datum #'_t))
         #'Nothing]))

    (define/contract declare-bindings (listof syntax?)
      (for/list ([(x t) (in-hash sigs)])
        (with-syntax* ([x (->id x)]
                       [T (ffi->trkt (datum->syntax src t))])
          #'[x T])))
    
    (let ([_ (log-info "Generating Typed Racket bindings...~n")]
          [stx #`(begin
                   (provide (all-from-out "types.rkt"))
                   (require/typed/provide "ffi.rkt"
                     #,@declare-bindings))])
      (parameterize ([pretty-print-columns 120])
        (printf "Generated typed module:~n")
        (pretty-write (syntax->datum stx)))
      (log-info "Finished generating Typed Racket bindings~n")
      stx)))

(splicing-let-syntax ([do-it! (λ (stx) (gen stx))])
  (do-it!))
