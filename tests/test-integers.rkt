#lang racket

(require rackunit)
(require "../smtlib2-parser.rkt")

(define/provide-test-suite test-integers
  (test-case
   "Test >, <, and +"
   (smt:with-context
    (smt:new-context-info)
    (smt:declare-fun a () Int)
    (smt:assert (> a 10))
    (smt:assert (< a 20))
    (check-eq? (smt:check-sat) 'sat)
    (define a-eval (smt:eval a))
    (check-true (and (> a-eval 10) (< a-eval 20)))
    (smt:assert (= (+ a 5) 14))
    (check-eq? (smt:check-sat) 'unsat))))