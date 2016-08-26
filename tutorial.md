z3-rkt tutorial
=========================================


Introduction
-----------------------------------------

This tutorial for the high-level Z3 interface in `z3-rkt` tries to mimic the
[Z3 guide](http://rise4fun.com/Z3/tutorial/guide).

To use the high-level interface, require the package:

```{racket}
#lang typed/racket/base
(require z3-rkt/smt)
```

All SMT commands should be executed within a `with-new-context` block:

```{racket}
(with-new-context ()
  ;; SMT commands within block
  ;; ...
  )
```

Alternatively, especially if you like to conveniently try the commands in the REPL,
you can initialize one globally shared context:

```{racket}
(init-global-context!)
;; SMT commands follow
;; ...
```

Basic Commands
-----------------------------------------

Command `declare-fun` declares a function, and `declare-const` declares a constant.
The latter is a short-hand for declaring a 0-arity function.
Command `assert!` adds a formula to the current Z3 internal stack.

All Z3 primitives are suffixed with `/s` to distinguish from Racket's.
Z3 primitives manipulate `Z3:Ast`s.
Racket numbers are coerced to `Z3:Ast`s when given as arguments to Z3 primitives
or declared functions.
A Racket symbol is resolved to the value mapped to in the current environment.
In the following example, `10` is coerced to a `Z3:Ast` representing the integer `10`,
and `'true` resolves to a `Z3:Ast` representing `true`.

```{racket}
(declare-const a Int)
(declare-fun f (Int Bool) Int)
(assert! (>/s a 10))
(assert! (</s (f a 'true) 100))
(check-sat)
; ==> 'sat : Z3:Sat-LBool
```

Notice that booleans are *not* coerced to `Z3:Ast`, because it is very easy to make
mistakes by confusing Racket's logical operators with Z3's.
For example, if `#f` were coerced to `Z3:Ast` representing `false` and we
mistakenly use `not` instead of `not/s`, we would get this confusing result:

```{racket}
(assert! (not (>/s 1 2)))
(check-sat)
; ==> 'unsat
```

Function and constant names can also by dynamically generated using `dynamic-declare-fun` and `dynamic-declare-const`.

TODO: `get-model`


### Using Scopes

We can do local commands using `with-local-stack`

```{racket}
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(with-local-stack
  (assert (= (+ x y) 10))
  (assert (= (+ x (* 2 y)) 20))
  (check-sat))
; ==> 'sat
(with-local-stack
  (assert (= (+ (* 3 x) y) 10))
  (assert (= (+ (* 2 x) (* 2 y)) 21))
  (check-sat)
  ; ==> 'unsat
  (dynamic-declare-const 'p 'Bool))
(assert (get-val 'p))
; ==> error, since declaration of `p` was removed from the stack
```

### Configuration

The `with-new-context` and `init-global-context!` accept optional arguments
to control Z3 behavior:

```{racket}
(with-new-context (#:timeout 500
                   #:unsat-core? #t
                   #:proof? #t)
  ;; Z3 commands
  ;; ...
  )
```

### Additional commands

TODO `simplify`
TODO `define-sort`


Propositional Logic
-----------------------------------------

```{racket}
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(define-fun conjecture () Bool
	(=>/s (and/s (=>/s p q) (=>/s q r))
		  (=>/s p r)))
(assert! (not/s conjecture))
(check-sat)
; ==> 'unsat
```

### Satisfiability and Validity

```{racket}
(declare-const a Bool)
(declare-const b Bool)
(define-fun demorgan () Bool
    (= (and a b) (not (or (not a) (not b)))))
(assert (not demorgan))
(check-sat)
; ==> 'unsat
```


Uninterpreted functions and constants
-----------------------------------------

```{racket}
(declare-fun f (Int) Int)
(declare-fun a () Int) ; a is a constant
(declare-const b Int) ; syntax sugar for (declare-fun b () Int)
(assert! (>/s a 20))
(assert! (>/s b a))
(assert! (=/s (f 10) 1))
(check-sat)
; TODO (get-model)
```

```{racket}
(declare-sort A)
(declare-const x A)
(declare-const y A)
(declare-fun f (A) A)
(assert! (=/s (f (f x)) x))
(assert! (=/s (f x) y))
(assert! (not/s (=/s x y)))
(check-sat)
; TODO (get-model)
```

Arithmatic
-----------------------------------------


Bitvectors
-----------------------------------------


Arrays
-----------------------------------------


Datatypes
-----------------------------------------


Quantifiers
-----------------------------------------

