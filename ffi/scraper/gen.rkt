#lang racket/base

(require (for-syntax racket/base
                     racket/match
                     racket/list
                     racket/set
                     racket/string
                     racket/syntax
                     syntax/parse
                     racket/contract
                     racket/function
                     racket/pretty
                     "scrape.rkt"
                     "conventions.rkt")
         syntax/parse/define
         racket/list
         racket/splicing
         ffi/unsafe
         racket/string
         racket/match)

(begin-for-syntax

  ;; Return the first index in `xs` whose element is equal to `x`
  (define (ith x xs)
    (for/first ([(xᵢ i) (in-indexed xs)] #:when (equal? xᵢ x))
      i))

  ;; Generate syntax for accessing the `ith` element of an `n`-sized tuple `tup`
  (define/contract (access-tuple tup n i)
    (syntax? exact-nonnegative-integer? exact-nonnegative-integer? . -> . syntax?)
    (with-syntax ([tup tup])
      (match* (n i)
        [(0 _) (error 'access-tuple "should not happen: 0-sized tuple")]
        [(1 _) #'tup]
        [(2 0) #'(map car tup)]
        [(2 1) #'(map cdr tup)]
        [(_ i)
         (with-syntax ([acc
                        (case i
                          [(0) #'first]
                          [(1) #'second]
                          [(2) #'third]
                          [(3) #'fourth])])
           #'(map acc tup))])))

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

    (define/contract (sig->_fun arg-names args tₐ)
      ((vectorof string?) list? string? . -> . (values syntax? (or/c #f 'pred 'bang)))
      ;(printf "sig->_fun: ~a ~a -> ~a~n" arg-names args tₐ)
      ;; Need to figure out:
      ;; - user-enter arguments
      ;; - computed arguments
      ;;   + _uint referenced as array length -> make it suplied
      ;;   + _array share length with another -> group
      ;; - out list
      ;;   + from annotation
      ;; - how to combine out and res
      ;;   + res is `bool`, 1-out -> conjunction
      ;;   + otherwise: (values res out ...), except if res is void, ditch
      ;; original list
      ;; array-index? : i → 𝔹
      ;; computed length
      ;; array-length-index serves as shared array's id

      ;; maintain:
      ;; - stack: user-enter args
      ;; - map: i → length(arg)
      ;; - map: i → parallel-array(arg)

      (define-syntax-rule (with-type-id [t v] e ...)
        (let-values ([(t _) (api-typ->rkt v)])
          (with-syntax ([t (->id t)])
            e ...)))

      ;; Indices to out parameters
      (define/contract outs (set/c fixnum? #:kind 'mutable) {mutable-seteq})

      ;; Map array index to the array with its lengths
      (define-values (array-indices-push! array-indices array-indices-count)
        (let ()
          (define/contract m
            (hash/c (cons/c boolean? fixnum?) (listof fixnum?))
            (make-hash))
          (values (λ (in? i j)
                    (hash-update! m (cons in? i) (λ (js) (cons j js)) '()))
                  (λ (in? i)
                    (reverse (hash-ref m (cons in? i) '())))
                  (λ () (hash-count m)))))

      ;; Identifiers for user-supplied arguments on Racket side
      (define-values (user-args-push! user-args)
        (let ()
          (define/contract args (listof identifier?) '())
          (values (λ (x) (set! args (cons x args)))
                  (λ () (reverse args)))))
      
      ;; Figure out array types and out parameters
      (for ([(arg i) (in-indexed args)])
        (match-define (cons in? t*) arg)
        (unless in?
          (set-add! outs i))
        (match t*
          [(? string? t)
           (void)]
          [(cons n t)
           (array-indices-push! in? n i)]))

      (define (array-name in? i)
        (string-join (for/list ([j (array-indices in? i)])
                       (vector-ref arg-names j))
                     "+"))
      
      ;; Figure out user-supplied arguments
      (for ([(arg i) (in-indexed args)])
        (match-define (cons in? t*) arg)
        (when (and in? (not (cons? t*)))
          (define name
            (match (array-indices in? i)
              ['() (vector-ref arg-names i)]
              [_   (array-name in? i)]))
          (user-args-push! (format-id #f "~a" name))))
      
      ;; Figure out input-description
      (define/contract ins (listof syntax?)
        (for/list ([(arg i) (in-indexed args)])
          (with-syntax ([xᵢ (format-id #f (vector-ref arg-names i))])
            (match-define (cons in? t*) arg)
            (cond
              [in?
               (match t*
                 [(? string? t)
                  (cond [(cons? (array-indices in? i))
                         (with-syntax ([lₛ (format-id #f "~a" (array-name in? i))])
                           #'(xᵢ : _uint = (length lₛ)))]
                        [else
                         (with-type-id [_t t]
                           #'(xᵢ : _t))])]
                 [(cons n t)
                  (define indices (array-indices in? n))
                  (define tup-size (length indices))
                  (define idx (ith i indices))
                  (with-syntax ([lₛ@i (access-tuple (format-id #f "~a" (array-name in? n))
                                                    tup-size
                                                    idx)])
                    (with-type-id [_t t]
                      (cond [(and (identifier? #'lₛ@i) (free-identifier=? #'lₛ@i #'xᵢ))
                             #'(xᵢ : (_list i _t))]
                            [else #`(xᵢ : (_list i _t) = lₛ@i)])))])]
              [else
               (match t*
                 [(? string? t)
                  (with-type-id [_t t]
                    #'(xᵢ : (_ptr o _t)))]
                 [(cons n t)
                  (with-syntax ([xₙ (format-id #f (vector-ref arg-names n))])
                    (with-type-id [_t t]
                      #`(xᵢ : (_list o _t xₙ))))])]))))
      
      (define/contract out-ids (listof syntax?)
        (for*/list ([(arg i) (in-indexed args)]
                    [in? (in-value (car arg))] #:unless in?)
          (format-id #f (vector-ref arg-names i))))

      (define/contract ans syntax?
        (let ([-values
               (match-lambda
                 [(list x) x]
                 [xs #`(values #,@xs)])])
          (match* (out-ids tₐ)
            [((list a) "BOOL")
             (case a
               [("BOOL") #`(and res (list #,a))]
               [else #`(and res #,a)])]
            [(_ "VOID")
             (cond [(null? out-ids) #`res]
                   [else (-values out-ids)])]
            [(_ _) (-values (cons #'res out-ids))])))


      (define sig-type
        (cond
          [(and (null? out-ids) (equal? "BOOL" tₐ)) 'pred]
          [(and (null? out-ids) (equal? "VOID" tₐ)) 'bang]
          [else #f]))

      (define sig
        (with-type-id [_tₐ tₐ]
          (with-syntax ([res-stx
                         (case tₐ
                           [("VOID") #'_void]
                           [else #'(res : _tₐ)])])
            (cond
              ; handle special cases to give cleaner signatures
              [(and (set-empty? out-ids) (zero? (array-indices-count)))
               (with-syntax ([(_tₓ ...)
                              (datum->syntax #f
                                             (for/list ([in ins])
                                               (syntax-parse in
                                                 [(_ : t _ ...) #'t])))])
                 #'(_fun _tₓ ... -> _tₐ))]
              [(and (set-empty? out-ids) (not (zero? (array-indices-count))))
               #`(_fun #,(user-args) :: #,@ins -> _tₐ)]
              [(and (not (set-empty? out-ids)) (zero? (array-indices-count)))
               #`(_fun #,@ins -> res-stx -> #,ans)]
              [else
               #`(_fun #,(user-args) :: #,@ins -> res-stx -> #,ans)]))))

      (define sig* ; try var-args for some cases
        (syntax-parse sig #:literals (_fun -> = length _uint _list)
          [(_fun (z₀:id ... zₙ:id) (~literal ::)
                 (x₀:id (~literal :) t₀:id) ...
                 (n:id (~literal :) _uint = (length lₙ:id))
                 (xₙ:id (~literal :) (_list (~literal i) tₙ))
                 -> res ...)
           ;; TODO didn't realize `syntax-parse` didn't allow non-linear patterns
           ;; Is there a nicer way to do this?
           #:when (and (free-identifier=? #'lₙ #'xₙ)
                       (free-identifier=? #'zₙ #'xₙ)
                       (andmap free-identifier=?
                               (syntax->list #'(z₀ ...))
                               (syntax->list #'(x₀ ...))))
           #'(_fun (x₀ ... . xₙ) ::
                   (x₀ : t₀) ...
                   (n : _uint = (length xₙ))
                   (xₙ : (_list i tₙ))
                   -> res ...)]
          [_ sig]))
      
      (values sig* sig-type))

    (define/contract define-bindings (listof syntax?)
      (for/list ([(f₀ tₐ) (in-hash api-ret)])
        (define args (hash-ref api-arg f₀))
        (define arg-names
          (match (hash-ref sig-arg f₀ #f)
            [#f (for/vector #:length (length args) ([(_ i) (in-indexed args)])
                  (format "x_~a" i))]
            [xs (for/vector #:length (length args) ([x xs])
                  (c-val->rkt (car x)))]))
        (define-values (sig type) (sig->_fun arg-names args tₐ))
        (with-syntax ([f (->id (c-fun->rkt f₀ #:type type))]
                      [f₀ (datum->syntax src f₀)]
                      [sig sig])
          (provides-add! #'f)
          #'(define-z3 f f₀ sig))))

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

(define-simple-macro (define-z3 x:id c-name:str t)
  (define x (get-ffi-obj c-name libz3 t)))

(splicing-let-syntax ([do-it (λ (stx) (gen stx))])
  (do-it))
