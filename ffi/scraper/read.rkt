#lang racket/base

(provide read-doc)

(require racket/match
         racket/list
         racket/string
         html
         xml
         )

(define regexp-junk #px"^([\\s])*$")

;; HTML -> (μ (X) String (Listof X))
;; Only retain non-empty texts from page, with some structure
(define (retain-text html)
  (for/list ([ctn (in-list (html-full-content html))]
             #:when (or (html-full? ctn)
                        (and (pcdata? ctn)
                             (string? (pcdata-string ctn))
                             (not (regexp-match? regexp-junk (pcdata-string ctn))))))
    (match ctn
      [(pcdata _ _ s) (string-trim s)]
      [_ (retain-text ctn)])))

;; Clean up empty and singleton lists
(define clean-up
  (match-lambda
    [(list x) (clean-up x)]
    [(? string? s) s]
    [xs
     (match (filter-not null? (map clean-up xs))
       [(list x) x]
       [xs* xs*])]))

(define (read-doc in)
  (log-info "Loading Z3 documentation from ~a...~n" in)
  (begin0 (clean-up (retain-text (read-html in)))
    (log-info "Finished loading documentation~n")))
