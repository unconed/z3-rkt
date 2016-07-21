#lang racket/base

(require (for-syntax racket/base
                     syntax/parse)
         syntax/parse/define
         "parser.rkt"
         "builtins.rkt")

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
     #'(begin
       (smt:declare-fun f (Tx ...) T)
       (smt:assert (∀/s ([x Tx] ...) (=/s (f x ...) e))))]))
(define-simple-macro (define-const c:id T e) (define-fun c:id () T e))

(provide
 (prefix-out
  smt:
  (combine-out define-fun define-const)))
