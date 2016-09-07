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
                     net/url
                     "scrape.rkt"
                     "conventions.rkt")
         syntax/parse/define
         racket/list
         racket/splicing
         ffi/unsafe
         racket/string
         racket/match)

(begin-for-syntax
  
  (define/contract stx-opaques (hash/c string? string?) (make-hash))

  ;; Return the first index in `xs` whose element is `equal?` to `x`
  (define (ith x xs)
    (for/first ([(xᵢ i) (in-indexed xs)] #:when (equal? xᵢ x))
      i))

  ;; Generate syntax for accessing the `ith` element of an `n`-sized tuple `tup`
  ;; Assume:
  ;; - 1-sized tuple is just itself
  ;; - 2-sized tuple is a `cons`
  ;; - 3+-sized tuple is a list
  (define/contract access-tuple
    (syntax? exact-nonnegative-integer? exact-nonnegative-integer? . -> . syntax?)
    (let ([accs (vector-immutable #'first #'second #'third #'fourth #'fifth
                                  #'sixth #'seventh #'eighth #'ninth #'tenth)])
      (λ (tup n i)
        (with-syntax ([tup tup])
          (match* (n i)
            [(0 _) (error 'access-tuple "cannot happen: 0-sized tuple")]
            [(1 _) #'tup]
            [(2 0) #'(map car tup)]
            [(2 1) #'(map cdr tup)]
            [(_ i)
             (with-syntax ([acc (vector-ref accs i)])
               #'(map acc tup))])))))
  
  (define ((gen-from-file src) fn)
    (printf "Attempt to generate Z3 bindings from local file ~a~n" fn)
    (gen src (open-input-file fn)))
  
  (define ((gen-from-http src) link)
    (printf "Attempt to generate Z3 bindings from ~a~n" link)
    (gen src (get-pure-port (string->url link))))

  ;; Generate untyped module given syntax source
  (define/contract (gen src in)
    (syntax? input-port? . -> . syntax?)
    
    (define (->id x) (format-id src "~a" x))

    (define-syntax-rule (with-type-id [t v] e ...)
      (with-syntax ([t (->id (api-typ->rkt v))])
        e ...))

    (define-values (api-ret api-arg sig-ret sig-arg opaques enums) (scrape in))

    ;; Add identifier to list of provides
    (define-values (provides-add! provides)
      (let ()
        (define/contract ps (listof identifier?) '())
        (values
         (λ (x) (set! ps (cons x ps)))
         (λ () (reverse ps)))))

    ;; Define opaque pointer types and provide the predicates
    (define/contract define-opaque-cpointers (listof syntax?)
      (let-values ([(_ts t?s)
                    (for/lists (_ts t?s) ([x opaques])
                      (c-typ->rkt x))])
        (for/list ([_t (in-list _ts)] [t? (in-list t?s)])
          (provides-add! (->id t?))
          (hash-set! stx-opaques _t t?)
          (with-syntax ([_t (->id _t)])
            #'(define-cpointer-type _t)))))

    ;; Define FFI mappings for enums
    (define/contract define-enums (listof syntax?)
      (for/list ([(t vs) (in-hash enums)])
        (define-values (_t _) (c-typ->rkt t))
        (with-syntax ([_t (->id _t)]
                      [(variant ...)
                       (datum->syntax
                        src
                        (append-map
                         (match-lambda
                           [(? string? s) (list (string->symbol (c-variant->rkt s)))]
                           [(cons s i) (let ([l (string->symbol (c-variant->rkt s))])
                                         `(,l = ,i))])
                         vs))])
          #'(define _t (_enum '(variant ...) _int32)))))

    ;; Generate FFI signature given argument names, types, and return type
    ;; Argument names are just for cosmetic reasons so I can debug internally
    (define/contract (sig->_fun arg-names args tₐ)
      ((vectorof string?) list? string? . -> . (values syntax? (or/c #f 'pred 'bang)))

      ;; Figure out which parameter holds the length to multiple arrays
      (define-values (get-array-indices num-array-indices)
        (let ([array-indices-map
               (for/fold ([array-indices-map (hash)])
                         ([(arg i) (in-indexed args)])
                 (match-define (cons in? t*) arg)
                 (match t*
                   [(cons n t)
                    (hash-update array-indices-map (cons in? n)
                                 (λ (is) (cons i is))
                                 '())]
                   [_ array-indices-map]))])
          (values (λ (in? i) (reverse (hash-ref array-indices-map (cons in? i) '())))
                  (hash-count array-indices-map))))

      (define/contract (get-list-id in? i) (boolean? fixnum? . -> . identifier?)
        (format-id #f "~a"
                   (string-join (for/list ([j (get-array-indices in? i)])
                                  (vector-ref arg-names j))
                                "+")))
      
      ;; List of Racket-supplied arguments for FFI function
      (define/contract user-args (listof identifier?) 
        (for*/list ([(arg i) (in-indexed args)]
                    [in? (in-value (car arg))] #:when in?
                    [t*  (in-value (cdr arg))] #:unless (cons? t*))
          (cond [(null? (get-array-indices in? i))
                 (format-id #f "~a" (vector-ref arg-names i))]
                [else (get-list-id in? i)])))
      
      ;; Input description for FFI signature
      (define/contract ins (listof syntax?)
        (for/list ([(arg i) (in-indexed args)])
          (with-syntax ([xᵢ (format-id #f (vector-ref arg-names i))])
            (match-define (cons in? t*) arg)
            (cond
              [in?
               (match t*
                 [(? string? t)
                  (cond [(cons? (get-array-indices in? i))
                         (with-syntax ([lₛ (get-list-id in? i)])
                           #'(xᵢ : _uint = (length lₛ)))]
                        [else
                         (with-type-id [_t t]
                           #'(xᵢ : _t))])]
                 [(cons n t)
                  (define indices (get-array-indices in? n))
                  (define tup-size (length indices))
                  (define idx (ith i indices))
                  (with-syntax ([lₛ@i (access-tuple (get-list-id in? n) tup-size idx)])
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
      
      ;; Out parameters for FFI function
      (define/contract outs (listof identifier?)
        (for*/list ([(arg i) (in-indexed args)]
                    [in? (in-value (car arg))] #:unless in?)
          (format-id #f (vector-ref arg-names i))))

      ;; Description for FFI function return
      (define/contract ans syntax?
        (let ([-values (match-lambda
                         [(list x) x]
                         [xs #`(values #,@xs)])])
          (match* (outs tₐ)
            [((list a) "BOOL")
             (case a
               [("BOOL") #`(and res (list #,a))]
               [else #`(and res #,a)])]
            [(_ "VOID") (if (null? outs) #'res (-values outs))]
            [(_ _) (-values (cons #'res outs))])))

      (define sig-type
        (cond [(and (null? outs) (equal? "BOOL" tₐ)) 'pred]
              [(and (null? outs) (equal? "VOID" tₐ)) 'bang]
              [else #f]))

      ;; FFI function signature, with cleaner output for special cases for debugging
      (define sig
        (with-type-id [_tₐ tₐ]
          (with-syntax ([res-stx
                         (case tₐ
                           [("VOID") #'_void]
                           [else #'(res : _tₐ)])])
            (cond
              [(and (null? outs) (zero? num-array-indices))
               (with-syntax ([(_tₓ ...)
                              (datum->syntax #f
                                             (for/list ([in ins])
                                               (syntax-parse in
                                                 [(_ : t _ ...) #'t])))])
                 #'(_fun _tₓ ... -> _tₐ))]
              [(and (null? outs) (not (zero? num-array-indices)))
               #`(_fun #,user-args :: #,@ins -> _tₐ)]
              [(and (not (null? outs)) (zero? num-array-indices))
               #`(_fun #,@ins -> res-stx -> #,ans)]
              [else
               #`(_fun #,user-args :: #,@ins -> res-stx -> #,ans)]))))

      ;; Same signature as `sig` but use varargs in some cases
      #;(define sig*
        (syntax-parse sig
          #:literals (_fun -> = length _uint _list)
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
      
      (values sig sig-type))

    ;; Define FFI bindings
    (define/contract define-bindings (listof syntax?)
      (for/list ([(f₀ tₐ) (in-hash api-ret)])
        (case f₀
          ;; HACK handle special cases separately because they accept null arguments
          [("Z3_mk_constructor")
           (with-syntax ([f (->id (c-fun->rkt f₀))]
                         [f₀ (datum->syntax src f₀)])
             (provides-add! #'f)
             #'(define-z3 f f₀
                 (_fun (c name recognizer field-names+sorts+sort-refs) ::
                       (c : _z3-context)
                       (name : _z3-symbol)
                       (recognizer : _z3-symbol)
                       (num-fields : _uint = (length field-names+sorts+sort-refs))
                       (field-names : (_list i _z3-symbol) = (map first field-names+sorts+sort-refs))
                       (sorts : (_list i _z3-sort/null) = (map second field-names+sorts+sort-refs))
                       (sort-refs : (_list i _uint) = (map third field-names+sorts+sort-refs))
                       -> _z3-constructor)))]
          [("Z3_mk_const")
           (with-syntax ([f (->id (c-fun->rkt f₀))]
                         [f₀ (datum->syntax src f₀)])
             (provides-add! #'f)
             #'(define-z3 f f₀ (_fun _z3-context _z3-symbol _z3-sort -> _z3-app)))]
          [else
           (define-values (sig type)
             (let* ([args (hash-ref api-arg f₀)]
                    [arg-names
                     (match (hash-ref sig-arg f₀ #f)
                       [#f (build-vector (length args) (λ (i) (format "x_~a" i)))]
                       [xs (for/vector #:length (length args) ([x xs])
                             (c-val->rkt (car x)))])]
                    [precise-ret
                     (match* (tₐ (hash-ref sig-ret f₀ #f))
                       [((or "UINT" "INT") (regexp #rx"^Z3_(.+)$" (list _ (? string? s))))
                        (string-upcase s)]
                       [(_ _) tₐ])])
               (sig->_fun arg-names args precise-ret)))
           (with-syntax ([f (->id (c-fun->rkt f₀ #:type type))]
                         [f₀ (datum->syntax src f₀)]
                         [sig sig])
             (provides-add! #'f)
             #'(define-z3 f f₀ sig))])))

    ;; Compile-time-communication of generated bindings
    (define stx-mk-opaques
      #`(list
         #,@(for/list ([(k v) stx-opaques])
              #`(cons #,k #,v))))
    (define stx-mk-enums
      (datum->syntax
       src
       (for/hash ([def define-enums])
         (syntax-parse def
           [((~literal define) t:id (_enum ((~literal quote) (v ...)) _))
            (values (syntax-e #'t)
                    (for*/list ([s (in-list (syntax->list #'(v ...)))]
                                [sᵥ (in-value (syntax-e s))]
                                #:when (symbol? sᵥ)
                                #:unless (equal? '= sᵥ))
                      sᵥ))]))))
    (define stx-mk-sigs
      (datum->syntax
       src
       (for/hash ([def define-bindings])
         (syntax-parse def
           [((~literal define-z3) f:id _ t)
            (values (syntax-e #'f) #'t)]))))

    (let ([_ (log-info "Generating Z3 FFI bindings...~n")]
          [stx #`(begin
                   (provide define-z3 #,@(provides)
                            (for-syntax opaques enums sigs))
                   #,@define-enums
                   #,@define-opaque-cpointers
                   #,@define-bindings
                   (begin
                     (define z3-null #f)
                     (define z3-null? not)
                     (provide z3-null z3-null?))
                   (define-for-syntax opaques #,stx-mk-opaques)
                   (define-for-syntax enums #,stx-mk-enums)
                   (define-for-syntax sigs #,stx-mk-sigs))])
      ;; Debug
      #;(parameterize ([pretty-print-columns 120])
        (printf "Generated untyped ffi:~n")
        (pretty-write (syntax->datum stx)))
      (log-info "Finished generating FFI bindings~n")
      stx)))

(define libz3
  (let-values
      ([(lib-name default-dir)
        (case (system-type 'os)
          [(unix) (values "libz3.so" #f)]
          [(windows) (values "z3.dll" #f)]
          [(macosx)
           (values "libz3.dylib"
                   ;; Homebrew puts it there
                   "/usr/local/lib/")])]
       [(Z3_LIB) "Z3_LIB"])
    (define libz3-path (or (getenv Z3_LIB) default-dir))
    (cond
      [libz3-path
       (define libz3-without-suffix
         (path-replace-extension (build-path libz3-path lib-name) ""))
       (ffi-lib libz3-without-suffix)]
      [else
       (error 'z3-rkt
              "Cannot locate Z3 libary. Please set ${~a} to the directory containing ~a"
              Z3_LIB
              lib-name)])))

(define-simple-macro (define-z3 x:id c-name:str t) (define x (get-ffi-obj c-name libz3 t)))

(splicing-let-syntax ([do-it!
                       (λ (stx)
                         (cond
                           [(getenv "Z3_DOC_LOCAL") => (gen-from-file stx)]
                           [(getenv "Z3_DOC_HTTP" ) => (gen-from-http stx)]
                           [else
                            ((gen-from-http stx)
                             "http://research.microsoft.com/en-us/um/redmond/projects/z3/code/group__capi.html")]))])
  (do-it!))
