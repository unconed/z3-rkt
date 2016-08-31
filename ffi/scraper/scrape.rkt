#lang typed/racket/base

(require racket/match
         racket/set
         racket/string
         racket/list)

(require/typed "read.rkt"
  [read-doc (Input-Port → Any)])

(define pat-def_API #rx"^.+_API\\('(.+)', *(.+), *\\((.*)\\) *\\)$")
(define pat-Z3_ #rx"^Z3_.+$")

;; Parse raw API description
(define (scrape [in : Input-Port])
  (define def-api-ret : (HashTable String String) (make-hash))
  (define def-api-arg : (HashTable String (Listof String)) (make-hash))
  (define sig-ret : (HashTable String String) (make-hash))
  (define sig-arg : (HashTable String (Listof (Pairof String String))) (make-hash))
  (define opaques     : (Setof String) {set})
  (define enums       : (HashTable String (Listof String)) (make-hash))

  (: on-def-API! : String String String → Void)
  (define (on-def-API! f ret args-str)
    (define args : (Listof String)
      ;; FIXME lol
      (match (string-split args-str "),")
        [(list xs ... x)
         (define xs* : (Listof String) (for/list ([xᵢ xs]) (format "~a)" xᵢ)))
         `(,@xs* ,x)]
        ['() '()]))
    (hash-set! def-api-ret f ret)
    (hash-set! def-api-arg f args))

  (: on-sig! : String String String → Void)
  (define (on-sig! f ret args-str)
    (printf "on-sig! ~a ~a ~a~n" f ret args-str)
    (hash-set! sig-ret f ret)
    (define args
      (match-let ([(regexp #rx"^\\((.*)\\)$" (list _ (? string? s))) args-str])
        (for/list : (Listof (Pairof String String)) ([arg-str (string-split s ",")]
                                                     #:unless (equal? arg-str "void"))
          (match-define ws (string-split arg-str " "))
          (define-values (ts xs) (split-at ws (sub1 (length ws))))
          (match (string-trim (car xs))
            [(regexp #rx"^\\*(.+)$" (list _ (? string? x)))
             (cons x (string-trim (string-join (append ts (list "*")))))]
            [x (cons x (string-trim (string-join ts)))]))))
    (hash-set! sig-arg f args))

  (: loop! : Any → Void)
  (define (loop! doc)
    (match doc
      [(and (? string?)
            (regexp pat-def_API (list _ (? string? x) (? string? ret) (? string? args-str))))
       (on-def-API! x ret args-str)]
      [(list (or (list (? string? ret) "Z3_API")
                 (list "BEGIN_MLAPI_EXCLUDE" (? string? ret) "Z3_API"))
             (list (? string? f  ) (? string? args-strs) ...))
       #:when ret
       (on-sig! f ret (string-join (cast args-strs (Listof String))))]
      [(list elems ...) (for-each loop! elems)]
      [_ (void)]))

  (loop! (read-doc in))

  (values def-api-ret
          def-api-arg
          sig-ret
          sig-arg
          opaques
          enums))

;; Debug
(define-values (def-api-ret def-api-arg sig-ret sig-arg opaques enums)
  (scrape (open-input-file "/tmp/Z3-api/Z3_ C API.html")))
(define api-ids (list->set (hash-keys def-api-ret)))
(define sig-ids (list->set (hash-keys sig-ret)))
(define api-not-sig (set-subtract api-ids sig-ids))
(define sig-not-api (set-subtract sig-ids api-ids))
