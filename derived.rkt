#lang typed/racket/base

(provide define-fun
         define-const)

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse
                     racket/pretty)
         racket/match
         syntax/parse/define
         "z3-wrapper.rkt"
         "environment.rkt"
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
     ;; FIXME: This can cause exponential blowup.
     ;; But I can't figure out how to use `macro-finder` from C API for now
     (define n (length (syntax->list #'(x ...))))
     #`(begin
         (define f : Z3:Func
           (let ([m : (HashTable (Listof Expr) Z3:Ast) (make-hash)])
             (match-lambda*
               [(and xs (list x ...))
                (hash-ref! m xs (λ () e))]
               [xs
                (error 'f "wrong arity. Expect ~a, given ~a arguments" #,n (length xs))])))
         (set-fun! 'f f))
     #;#'(begin
       (smt:declare-fun f (Tx ...) T)
       (smt:assert (∀/s ([x Tx] ...) (=/s (f x ...) e))))]))
(define-simple-macro (define-const c:id T e) (define-fun c:id () T e))


