#lang racket/base

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse
                     racket/pretty)
         syntax/parse/define
         "parser.rkt"
         "builtins.rkt")

(define-syntax (define/memo stx)
  (syntax-parse stx
    [(_ (f:id x:id) e ...)
     #'(define f
         (let ([m (make-hash)])
           (λ (x)
             (hash-ref! m x (λ () e ...)))))]
    [(_ (f:id x:id ...) e ...)
     (define ast
       #'(define f
           (let ([m (make-hash)])
             (λ (x ...)
               (hash-ref! m (list x ...) (λ () e ...))))))
     ;(printf "define-fun:~n")
     ;(pretty-print (syntax->datum ast))
     ast]))

;; Functions that are written in terms of the base functions in main.rkt and
;; builtins.rkt.

;; Define a function using universal quantifiers as a sort of macro.
;; Note that defining recursive functions is possible but highly
;; recommended against.
(define-syntax (define-fun stx)
  (syntax-parse stx
    [(_ c:id () T e)
     #'(begin
       (smt:declare-const c () T)
       (smt:assert (=/s c e)))]
    [(_ f:id ([x:id Tx] ...) T e)
     ;; FIXME: This can cause exponential blowup.
     ;; But I can't figure out how to use `macro-finder` from C API for now
     #'(define/memo (f x ...) e)
     #;#'(begin
       (smt:declare-fun f (Tx ...) T)
       (smt:assert (∀/s ([x Tx] ...) (=/s (f x ...) e))))]))
(define-simple-macro (define-const c:id T e) (define-fun c:id () T e))

(provide
 (prefix-out
  smt:
  (combine-out define-fun define-const)))
