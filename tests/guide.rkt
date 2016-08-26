#lang typed/racket/base

;; These tests are from examples from the Z3 guide
;; http://rise4fun.com/Z3/tutorial/guide

(require typed/rackunit
         "../smt/main.rkt")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Basic Commands
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(check-equal?
 (with-new-context ()
   (declare-const a Int)
   (declare-fun f (Int Bool) Int)
   (assert! (>/s a 10))
   (assert! (</s (f a 'true) 100))
   (check-sat))
 'sat)

(with-new-context ()
  (declare-const x Int)
  (declare-const y Int)
  (declare-const z Int)
  (with-local-stack
    (assert! (=/s (+/s x y) 10))
    (assert! (=/s (+/s x (*/s 2 y)) 20))
    (check-equal? (check-sat) 'sat))
  (with-local-stack
    (assert! (=/s (+/s (*/s 3 x) y) 10))
    (assert! (=/s (+/s (*/s 2 x) (*/s 2 y)) 21))
    (check-equal? (check-sat) 'unsat)
    (dynamic-declare-const 'p 'Bool))
  (check-exn exn:fail? (λ () (assert! (get-val 'p)))))

;; TODO: parameterized sort
#;(with-new-context ()
  (define-sort Set (T) (Array T Bool))
  (define-sort IList () (List Int))
  (define-sort List-Set (T) (Array (List T) Bool))
  (define-sort I () Int)

  (declare-const s1 (Set I))
  (declare-const s2 (List-Set Int))
  (declare-const a I)
  (declare-const l IList)

  (assert (= (select s1 a) true))
  (assert (= (select s2 l) false))
  (check-sat))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Propositional Logic
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(with-new-context ()
  (declare-const p Bool)
  (declare-const q Bool)
  (declare-const r Bool)
  (define-fun conjecture () Bool
    (=>/s (and/s (=>/s p q) (=>/s q r))
          (=>/s p r)))
  (assert! (not/s conjecture))
  (check-equal? (check-sat) 'unsat))

(with-new-context ()
  (declare-const a Bool)
  (declare-const b Bool)
  (define-fun demorgan () Bool
    (=/s (and/s a b) (not/s (or/s (not/s a) (not/s b)))))
  (assert! (not/s demorgan))
  (check-equal? (check-sat) 'unsat))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Uninterpreted functions and constants
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(with-new-context ()
  (declare-sort A)
  (declare-const x A)
  (declare-const y A)
  (declare-fun f (A) A)
  (assert! (=/s (f (f x)) x))
  (assert! (=/s (f x) y))
  (assert! (not/s (=/s x y)))
  (check-equal? (check-sat) 'sat))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Arithmetic
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(check-equal?
 (with-new-context ()
   (declare-const a Int)
   (declare-const b Int)
   (declare-const c Int)
   (declare-const d Real)
   (declare-const e Real)
   (assert! (>/s a (+/s b 2)))
   (assert! (=/s a (+/s (*/s 2 c) 10)))
   (assert! (<=/s (+/s c b) 1000))
   (assert! (>=/s d e))
   (check-sat))
 'sat)

(check-equal?
 (with-new-context ()
   (declare-const a Int)
   (declare-const b Int)
   (declare-const c Int)
   (declare-const d Real)
   (declare-const e Real)
   (assert! (>/s e (+/s (to-real/s (+/s a b)) 2.0)))
   (assert! (=/s d (+/s (to-real/s c) 0.5)))
   (assert! (>/s a b))
   (check-sat))
 'sat)

(check-equal?
 (with-new-context ()
   (declare-const a Int)
   (assert! (>/s (*/s a a) 3))
   (check-sat))
 'sat)

(check-equal?
 (with-new-context ()
   (declare-const b Real)
   (declare-const c Real)
   (assert! (=/s (+/s (*/s b b b) (*/s b c)) 3.0))
   (check-sat))
 'sat)

(check-equal?
 (with-new-context ()
   (declare-const x Real)
   (declare-const y Real)
   (declare-const z Real)
   (assert! (=/s (*/s x x) (+/s x 2.0)))
   (assert! (=/s (*/s x y) x))
   (assert! (=/s (*/s (-/s y 1.0) z) 1.0))
   (check-sat))
 'unsat)

(check-equal?
 (with-new-context ()
   (declare-const b Real)
   (declare-const c Real)
   (assert! (=/s (+/s (*/s b b b) (*/s b c)) 3.0))
   (check-sat))
 'sat)

(check-equal?
 (with-new-context ()
   (declare-const a Int)
   (declare-const r1 Int)
   (declare-const r2 Int)
   (declare-const r3 Int)
   (declare-const r4 Int)
   (declare-const r5 Int)
   (declare-const r6 Int)
   (assert! (=/s a 10))
   (assert! (=/s r1 (div/s a 4))) ; integer division
   (assert! (=/s r2 (mod/s a 4))) ; mod
   (assert! (=/s r3 (rem/s a 4))) ; remainder
   (assert! (=/s r4 (div/s a (-/s 4)))) ; integer division
   (assert! (=/s r5 (mod/s a (-/s 4)))) ; mod
   (assert! (=/s r6 (rem/s a (-/s 4)))) ; remainder
   (declare-const b Real)
   (declare-const c Real)
   (assert! (>=/s b (//s c 3.0)))
   (assert! (>=/s c 20.0))
   (check-sat))
 'sat)

(check-equal?
 (with-new-context ()
   (define-fun mydiv ((x Real) (y Real)) Real
     (ite/s (not/s (=/s y 0.0))
            (//s x y)
            0.0))
   (declare-const a Real)
   (declare-const b Real)
   (assert! (>=/s (mydiv a b) 1.0))
   (assert! (=/s b 0.0))
   (check-sat))
 'unsat)
