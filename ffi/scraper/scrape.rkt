#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         racket/string
         racket/list)

(require/typed "read.rkt"
  [read-doc (Input-Port → Any)])

(define pat-def_API #rx"^.+_API\\('(.+)', *(.+), *\\((.*)\\) *\\)$")
(define pat-Z3_ #rx"^Z3_.+$")

(: string->fixnum : String → Fixnum)
(define string->fixnum
  (match-lambda
    [(regexp #rx"^0x(.+)$" (list _ (? string? s)))
     (assert (string->number (format "#x~a" s)) fixnum?)]
    [s (assert (string->number s) fixnum?)]))

;; Parse raw API description
(define (scrape [in : Input-Port])
  (define api-ret : (HashTable String String) (make-hash))
  (define api-arg : (HashTable String (Listof (Pairof Boolean (U String (Pairof Nonnegative-Fixnum String))))) (make-hash))
  (define sig-ret : (HashTable String String) (make-hash))
  (define sig-arg : (HashTable String (Listof (Pairof String String))) (make-hash))
  (define types     : (Setof String) {set})
  (define enums     : (HashTable String (Listof (U String (Pairof String Fixnum)))) (make-hash))
  (define deprecated : (Setof String) {set})

  (define (types-add! [s : String])
    (when (regexp-match? #rx"^Z3_.+$" s)
      (set! types (set-add types s))))

  (: on-def-API! : String String String → Void)
  (define (on-def-API! f ret args-str)
    ;(printf "on-def-API!: ~a ~a ~a~n" f ret args-str)
    (define arg-desc-strs : (Listof String)
      ;; FIXME lol
      (match (string-split (string-trim args-str) "),")
        [(list x)
         (list (format "~a)" x))]
        [(list xs ... x)
         (define xs* : (Listof String) (for/list ([xᵢ xs]) (format "~a)" xᵢ)))
         `(,@xs* ,x)]
        ['() '()]))
    (define arg-descs : (Listof (Pairof Boolean (U String
                                                   (Pairof Nonnegative-Fixnum String))))
      (for/list ([str arg-desc-strs])
        (match str
          [(regexp #rx"^ *_in\\((.+)\\) *$"
                   (list _ (? string? s)))
           (cons #t (string-trim s))]
          [(regexp #rx"^ *_out\\((.+)\\) *$"
                   (list _ (? string? s)))
           (cons #f (string-trim s))]
          [(regexp #rx"^ *_in.*_array\\((.+), *(.+)\\) *"
                   (list _ (? string? i) (? string? s)))
           ;; TODO what does `_inout_array` mean? Treating it like `_in_array` for now
           (list* #t
                  (assert (string->fixnum (string-trim i)) exact-nonnegative-integer?)
                  (string-trim s))]
          [(regexp #rx"^ *_out.*_array\\((.+), *(.+)\\) *"
                   (list _ (? string? i) (? string? s)))
           ;; TODO ok to treat `_out_managed_array` as just `_out_array`?
           (list* #f
                  (assert (string->fixnum (string-trim i)) exact-nonnegative-integer?)
                  (string-trim s))])))
    (hash-set! api-ret f ret)
    (hash-set! api-arg f arg-descs))

  (: on-sig! : String String String → Void)
  (define (on-sig! f ret args-str)
    ;(printf "on-sig! ~a ~a ~a~n" f ret args-str)
    (define args
      (match-let ([(regexp #rx"^\\((.*)\\)$" (list _ (? string? s))) args-str])
        (for/list : (Listof (Pairof String String)) ([arg-str (string-split s ",")]
                                                     #:unless (equal? arg-str "void"))
          (match-define ws (string-split arg-str " "))
          (match-define-values (ts (list x)) (split-at ws (sub1 (length ws))))

          ;; Shift `*` from name to type
          (match (string-trim x)
            [(regexp #rx"^\\*(.+)$" (list _ (? string? x₁)))
             (set! ts (append ts (list "*")))
             (set! x x₁)]
            [_ (void)])

          ;; Shift `[]` from name to type
          (match (string-trim x)
            [(regexp #rx"^(.+) *\\[\\]$" (list _ (? string? x₁)))
             (set! ts (append ts (list "[]")))
             (set! x x₁)]
            [_ (void)])

          (cons x (string-join ts)))))
    (hash-set! sig-arg f args)
    (hash-set! sig-ret f ret)
    (types-add! ret))

  (: on-opaque! : Any → Void)
  (define on-opaque!
    (match-lambda
      [(and (? string?)
            (regexp #px"^Z3_([\\w]+):.*$" (list _ (? string? typ))))
       (types-add! (format "Z3_~a" typ))]
      [(? list? xs) (for-each on-opaque! xs)]
      [_ (void)]))

  (: on-enum! : String (Listof String) → Void)
  (define (on-enum! t v-strs)
    (define vs
      (for/list : (Listof (U String (Pairof String Fixnum))) ([v-str v-strs])
        (match v-str
          [(regexp #rx"^(.+)=(.+)$" (list _ (? string? l) (? string? r)))
           (cons (string-trim l) (string->fixnum (string-trim r)))]
          [s (string-trim s)])))
    (hash-set! enums (string-trim t) vs))

  (: loop! : Any → Void)
  (define (loop! doc)
    (match doc
      ;; Search for `def_API` lines
      [(and (? string?)
            (regexp pat-def_API (list _ (? string? x) (? string? ret) (? string? args-str))))
       (unless (set-member? deprecated x)
         (on-def-API! x ret args-str))]
      ;; Search for signature lines
      [(list (or (list (? string? ret) "Z3_API")
                 (list "BEGIN_MLAPI_EXCLUDE" (? string? ret) "Z3_API"))
             (list (? string? f) (? string? args-strs) ...))
       #:when ret
       (unless (set-member? deprecated f)
         (on-sig! f ret (string-join (cast args-strs (Listof String)))))]
      ;; Search for mentions of opaque pointers
      [(list (and (? string?) (regexp #rx".*opaque.*")) rst ...)
       (for-each on-opaque! rst)]
      ;; Search for mentions of enums
      [(list "enum" (list (? string? t) "{" (? string? vs) ... "}"))
       (on-enum! t (string-split (string-join (cast vs (Listof String))) "," #:trim? #t))]
      ;; Recursively search for stuff
      [(list elems ...) (for-each loop! elems)]
      [_ (void)]))

  (: maybe-add-deprecated! : Any → Void)
  (define maybe-add-deprecated!
    (match-lambda
      [(list (list _ "Z3_API")
             (list (? string? f) _ ...))
       (set! deprecated (set-add deprecated f))]
      [_ (void)]))
  
  (: loop-for-deprecated! : Any → Void)
  (define loop-for-deprecated!
    (match-lambda
      [(list (and (? string?) (regexp #rx"^Deprecated.*$")) rst ...)
       (for-each maybe-add-deprecated! rst)]
      [(list xs ...)
       (for-each loop-for-deprecated! xs)]
      [_ (void)]))

  (let ([doc (read-doc in)])
    (loop-for-deprecated! doc)
    (loop! doc))

  (values api-ret
          api-arg
          sig-ret
          sig-arg
          (set-subtract types (list->set (hash-keys enums)))
          enums))
