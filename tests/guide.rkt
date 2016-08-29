#lang typed/racket/base

;; These tests are from examples from the Z3 guide
;; http://rise4fun.com/Z3/tutorial/guide

(require typed/rackunit
         "../smt/main.rkt")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Basic Commands
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(check-equal?
 (with-new-context
   (declare-const a Int/s)
   (declare-fun f (Int/s Bool/s) Int/s)
   (assert! (>/s a 10))
   (assert! (</s (f a true/s) 100))
   (check-sat))
 'sat)

(with-new-context
  (declare-const x Int/s)
  (declare-const y Int/s)
  (declare-const z Int/s)
  (with-local-stack
    (assert! (=/s (+/s x y) 10))
    (assert! (=/s (+/s x (*/s 2 y)) 20))
    (check-equal? (check-sat) 'sat))
  (with-local-stack
    (assert! (=/s (+/s (*/s 3 x) y) 10))
    (assert! (=/s (+/s (*/s 2 x) (*/s 2 y)) 21))
    (check-equal? (check-sat) 'unsat)
    (dynamic-declare-const 'p Bool/s))
  (check-exn exn:fail? (λ () (assert! (val-of 'p)))))

;; TODO: parameterized sort
#;(with-new-context
  (define-sort Set (T) (Array T Bool/s))
  (define-sort IList () (List Int/s))
  (define-sort List-Set (T) (Array (List T) Bool/s))
  (define-sort I () Int/s)

  (declare-const s1 (Set I))
  (declare-const s2 (List-Set Int/s))
  (declare-const a I)
  (declare-const l IList)

  (assert (= (select s1 a) true))
  (assert (= (select s2 l) false))
  (check-sat))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Propositional Logic
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(with-new-context
  (declare-const p Bool/s)
  (declare-const q Bool/s)
  (declare-const r Bool/s)
  (define-fun conjecture () Bool/s
    (=>/s (and/s (=>/s p q) (=>/s q r))
          (=>/s p r)))
  (assert! (not/s conjecture))
  (check-equal? (check-sat) 'unsat))

(with-new-context
  (declare-const a Bool/s)
  (declare-const b Bool/s)
  (define-fun demorgan () Bool/s
    (=/s (and/s a b) (not/s (or/s (not/s a) (not/s b)))))
  (assert! (not/s demorgan))
  (check-equal? (check-sat) 'unsat))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Uninterpreted functions and constants
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(with-new-context
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
 (with-new-context
   (declare-const a Int/s)
   (declare-const b Int/s)
   (declare-const c Int/s)
   (declare-const d Real/s)
   (declare-const e Real/s)
   (assert! (>/s a (+/s b 2)))
   (assert! (=/s a (+/s (*/s 2 c) 10)))
   (assert! (<=/s (+/s c b) 1000))
   (assert! (>=/s d e))
   (check-sat))
 'sat)

(check-equal?
 (with-new-context
   (declare-const a Int/s)
   (declare-const b Int/s)
   (declare-const c Int/s)
   (declare-const d Real/s)
   (declare-const e Real/s)
   (assert! (>/s e (+/s (to-real/s (+/s a b)) 2.0)))
   (assert! (=/s d (+/s (to-real/s c) 0.5)))
   (assert! (>/s a b))
   (check-sat))
 'sat)

(check-equal?
 (with-new-context
   (declare-const a Int/s)
   (assert! (>/s (*/s a a) 3))
   (check-sat))
 'sat)

(check-equal?
 (with-new-context
   (declare-const b Real/s)
   (declare-const c Real/s)
   (assert! (=/s (+/s (*/s b b b) (*/s b c)) 3.0))
   (check-sat))
 'sat)

(check-equal?
 (with-new-context
   (declare-const x Real/s)
   (declare-const y Real/s)
   (declare-const z Real/s)
   (assert! (=/s (*/s x x) (+/s x 2.0)))
   (assert! (=/s (*/s x y) x))
   (assert! (=/s (*/s (-/s y 1.0) z) 1.0))
   (check-sat))
 'unsat)

(check-equal?
 (with-new-context
   (declare-const b Real/s)
   (declare-const c Real/s)
   (assert! (=/s (+/s (*/s b b b) (*/s b c)) 3.0))
   (check-sat))
 'sat)

(check-equal?
 (with-new-context
   (declare-const a Int/s)
   (declare-const r1 Int/s)
   (declare-const r2 Int/s)
   (declare-const r3 Int/s)
   (declare-const r4 Int/s)
   (declare-const r5 Int/s)
   (declare-const r6 Int/s)
   (assert! (=/s a 10))
   (assert! (=/s r1 (div/s a 4))) ; integer division
   (assert! (=/s r2 (mod/s a 4))) ; mod
   (assert! (=/s r3 (rem/s a 4))) ; remainder
   (assert! (=/s r4 (div/s a (-/s 4)))) ; integer division
   (assert! (=/s r5 (mod/s a (-/s 4)))) ; mod
   (assert! (=/s r6 (rem/s a (-/s 4)))) ; remainder
   (declare-const b Real/s)
   (declare-const c Real/s)
   (assert! (>=/s b (//s c 3.0)))
   (assert! (>=/s c 20.0))
   (check-sat))
 'sat)

(check-equal?
 (with-new-context
   (define-fun mydiv ((x Real/s) (y Real/s)) Real/s
     (ite/s (not/s (=/s y 0.0))
            (//s x y)
            0.0))
   (declare-const a Real/s)
   (declare-const b Real/s)
   (assert! (>=/s (mydiv a b) 1.0))
   (assert! (=/s b 0.0))
   (check-sat))
 'unsat)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Bitvectors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Arrays
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(check-equal?
 (with-new-context
   (declare-const x Int/s)
   (declare-const y Int/s)
   (declare-const z Int/s)
   (declare-const a1 (Array/s Int/s Int/s))
   (declare-const a2 (Array/s Int/s Int/s))
   (declare-const a3 (Array/s Int/s Int/s))
   (assert! (=/s (select/s a1 x) x))
   (assert! (=/s (store/s a1 x y) a1))
   (check-sat)) ; TODO get-model
 'sat)

(check-equal?
 (with-new-context
   (declare-const x Int/s)
   (declare-const y Int/s)
   (declare-const z Int/s)
   (declare-const a1 (Array/s Int/s Int/s))
   (declare-const a2 (Array/s Int/s Int/s))
   (declare-const a3 (Array/s Int/s Int/s))
   (assert! (=/s (select/s a1 x) x))
   (assert! (=/s (store/s a1 x y) a1))
   (assert! (not/s (=/s x y)))
   (check-sat))
 'unsat)

;; TODO Constant Arrays
;; TODO Mapping Functions on Arrays


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Datatypes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO records (parameterized)

(with-new-context
  (declare-datatypes () ((S A B C)))
  (declare-const x S)
  (declare-const y S)
  (declare-const z S)
  (declare-const u S)
  (assert! (distinct/s x y z))
  (check-equal? (check-sat) 'sat)
  (assert! (distinct/s x y z u))
  (check-equal? (check-sat) 'unsat))

;; TODO Recursive datatypes (parameterized)

;; TODO: Mutually recursive datatypes (parameterized)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Quantifiers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(check-equal?
 (with-new-context
   (declare-sort Type)
   (declare-fun subtype (Type Type) Bool/s)
   (declare-fun array-of (Type) Type)
   (assert! (∀/s ((x Type)) (subtype x x)))
   (assert! (∀/s ((x Type) (y Type) (z Type))
                 (=>/s (and/s (subtype x y) (subtype y z)) 
                       (subtype x z)))) 
   (assert! (∀/s ((x Type) (y Type))
                 (=>/s (and/s (subtype x y) (subtype y x)) 
                       (=/s x y))))
   (assert! (∀/s ((x Type) (y Type) (z Type))
                 (=>/s (and/s (subtype x y) (subtype x z)) 
                       (or/s (subtype y z) (subtype z y))))) 
   (assert! (∀/s ((x Type) (y Type))
                 (=>/s (subtype x y) 
                       (subtype (array-of x) (array-of y)))))
   (declare-const root-type Type)
   (assert! (∀/s ((x Type)) (subtype x root-type)))
   (check-sat))
 'sat)

(check-equal?
 (with-new-context
   (set-options! #:auto-config? #f
                 #:mbqi? #f
                 #:timeout 2000)
   (declare-fun f (Int/s) Int/s)
   (declare-fun g (Int/s) Int/s)
   (declare-const a Int/s)
   (declare-const b Int/s)
   (declare-const c Int/s)
   (assert! (∀/s ((x Int/s))
                 (=/s (f (g x)) x)
                 #:pattern (list (pattern-of (f (g x))))))
   (assert! (=/s (g a) c))
   (assert! (=/s (g b) c))
   (assert! (not/s (=/s a b)))
   (check-sat))
 'unknown)

(check-equal?
 (with-new-context
   (declare-sort A)
   (declare-sort B)
   (declare-fun f (A) B)
   (assert! (∀/s ((x A) (y A))
                 (=>/s (=/s (f x) (f y)) (=/s x y))
                 #:pattern (list (pattern-of (f x) (f y)))))
   (declare-const a1 A)
   (declare-const a2 A)
   (declare-const b B)
   (assert! (not/s (=/s a1 a2)))
   (assert! (=/s (f a1) b))
   (assert! (=/s (f a2) b))
   (check-sat))
 'unsat)
