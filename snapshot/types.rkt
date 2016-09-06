#lang typed/racket/base

(provide Z3-Parameter-Kind
         Z3-Ast-Kind
         Z3-Decl-Kind
         Z3-Ast-Print-Mode
         Z3-Symbol-Kind
         Z3-Search-Failure
         Z3-Goal-Prec
         Z3-Lbool
         Z3-Param-Kind
         Z3-Sort-Kind
         Z3-Error-Code)

(require ffi/unsafe
         racket/splicing
         "ffi.rkt")

(define-type
  Z3-Parameter-Kind
  (U
   'parameter-int
   'parameter-double
   'parameter-rational
   'parameter-symbol
   'parameter-sort
   'parameter-ast
   'parameter-func-decl))
(define-type Z3-Ast-Kind (U 'numeral-ast 'app-ast 'var-ast 'quantifier-ast 'sort-ast 'func-decl-ast 'unknown-ast))
(define-type
  Z3-Decl-Kind
  (U
   'op-true
   'op-false
   'op-eq
   'op-distinct
   'op-ite
   'op-and
   'op-or
   'op-iff
   'op-xor
   'op-not
   'op-implies
   'op-oeq
   'op-interp
   'op-anum
   'op-agnum
   'op-le
   'op-ge
   'op-lt
   'op-gt
   'op-add
   'op-sub
   'op-uminus
   'op-mul
   'op-div
   'op-idiv
   'op-rem
   'op-mod
   'op-to-real
   'op-to-int
   'op-is-int
   'op-power
   'op-store
   'op-select
   'op-const-array
   'op-array-map
   'op-array-default
   'op-set-union
   'op-set-intersect
   'op-set-difference
   'op-set-complement
   'op-set-subset
   'op-as-array
   'op-bnum
   'op-bit1
   'op-bit0
   'op-bneg
   'op-badd
   'op-bsub
   'op-bmul
   'op-bsdiv
   'op-budiv
   'op-bsrem
   'op-burem
   'op-bsmod
   'op-bsdiv0
   'op-budiv0
   'op-bsrem0
   'op-burem0
   'op-bsmod0
   'op-uleq
   'op-sleq
   'op-ugeq
   'op-sgeq
   'op-ult
   'op-slt
   'op-ugt
   'op-sgt
   'op-band
   'op-bor
   'op-bnot
   'op-bxor
   'op-bnand
   'op-bnor
   'op-bxnor
   'op-concat
   'op-sign-ext
   'op-zero-ext
   'op-extract
   'op-repeat
   'op-bredor
   'op-bredand
   'op-bcomp
   'op-bshl
   'op-blshr
   'op-bashr
   'op-rotate-left
   'op-rotate-right
   'op-ext-rotate-left
   'op-ext-rotate-right
   'op-int2bv
   'op-bv2int
   'op-carry
   'op-xor3
   'op-pr-undef
   'op-pr-true
   'op-pr-asserted
   'op-pr-goal
   'op-pr-modus-ponens
   'op-pr-reflexivity
   'op-pr-symmetry
   'op-pr-transitivity
   'op-pr-transitivity-star
   'op-pr-monotonicity
   'op-pr-quant-intro
   'op-pr-distributivity
   'op-pr-and-elim
   'op-pr-not-or-elim
   'op-pr-rewrite
   'op-pr-rewrite-star
   'op-pr-pull-quant
   'op-pr-pull-quant-star
   'op-pr-push-quant
   'op-pr-elim-unused-vars
   'op-pr-der
   'op-pr-quant-inst
   'op-pr-hypothesis
   'op-pr-lemma
   'op-pr-unit-resolution
   'op-pr-iff-true
   'op-pr-iff-false
   'op-pr-commutativity
   'op-pr-def-axiom
   'op-pr-def-intro
   'op-pr-apply-def
   'op-pr-iff-oeq
   'op-pr-nnf-pos
   'op-pr-nnf-neg
   'op-pr-nnf-star
   'op-pr-cnf-star
   'op-pr-skolemize
   'op-pr-modus-ponens-oeq
   'op-pr-th-lemma
   'op-pr-hyper-resolve
   'op-ra-store
   'op-ra-empty
   'op-ra-is-empty
   'op-ra-join
   'op-ra-union
   'op-ra-widen
   'op-ra-project
   'op-ra-filter
   'op-ra-negation-filter
   'op-ra-rename
   'op-ra-complement
   'op-ra-select
   'op-ra-clone
   'op-fd-lt
   'op-label
   'op-label-lit
   'op-dt-constructor
   'op-dt-recogniser
   'op-dt-accessor
   'op-dt-update-field
   'op-pb-at-most
   'op-pb-le
   'op-pb-ge
   'op-fpa-rm-nearest-ties-to-even
   'op-fpa-rm-nearest-ties-to-away
   'op-fpa-rm-toward-positive
   'op-fpa-rm-toward-negative
   'op-fpa-rm-toward-zero
   'op-fpa-num
   'op-fpa-plus-inf
   'op-fpa-minus-inf
   'op-fpa-nan
   'op-fpa-plus-zero
   'op-fpa-minus-zero
   'op-fpa-add
   'op-fpa-sub
   'op-fpa-neg
   'op-fpa-mul
   'op-fpa-div
   'op-fpa-rem
   'op-fpa-abs
   'op-fpa-min
   'op-fpa-max
   'op-fpa-fma
   'op-fpa-sqrt
   'op-fpa-round-to-integral
   'op-fpa-eq
   'op-fpa-lt
   'op-fpa-gt
   'op-fpa-le
   'op-fpa-ge
   'op-fpa-is-nan
   'op-fpa-is-inf
   'op-fpa-is-zero
   'op-fpa-is-normal
   'op-fpa-is-subnormal
   'op-fpa-is-negative
   'op-fpa-is-positive
   'op-fpa-fp
   'op-fpa-to-fp
   'op-fpa-to-fp-unsigned
   'op-fpa-to-ubv
   'op-fpa-to-sbv
   'op-fpa-to-real
   'op-fpa-to-ieee-bv
   'op-uninterpreted))
(define-type
  Z3-Ast-Print-Mode
  (U 'print-smtlib-full 'print-low-level 'print-smtlib-compliant 'print-smtlib2-compliant))
(define-type Z3-Symbol-Kind (U 'int-symbol 'string-symbol))
(define-type
  Z3-Search-Failure
  (U 'no-failure 'unknown 'timeout 'memout-watermark 'canceled 'num-conflicts 'theory 'quantifiers))
(define-type Z3-Goal-Prec (U 'goal-precise 'goal-under 'goal-over 'goal-under-over))
(define-type Z3-Lbool (U 'l-false 'l-undef 'l-true))
(define-type Z3-Param-Kind (U 'pk-uint 'pk-bool 'pk-double 'pk-symbol 'pk-string 'pk-other 'pk-invalid))
(define-type
  Z3-Sort-Kind
  (U
   'uninterpreted-sort
   'bool-sort
   'int-sort
   'real-sort
   'bv-sort
   'array-sort
   'datatype-sort
   'relation-sort
   'finite-domain-sort
   'floating-point-sort
   'rounding-mode-sort
   'unknown-sort))
(define-type
  Z3-Error-Code
  (U
   'ok
   'sort-error
   'iob
   'invalid-arg
   'parser-error
   'no-parser
   'invalid-pattern
   'memout-fail
   'file-access-error
   'internal-fatal
   'invalid-usage
   'dec-ref-error
   'exception))

(require/typed/provide "ffi.rkt"
  (#:opaque Z3-Fixedpoint z3-fixedpoint?)
  (#:opaque Z3-Param-Descrs z3-param-descrs?)
  (#:opaque Z3-Solver z3-solver?)
  (#:opaque Z3-Constructor z3-constructor?)
  (#:opaque Z3-Ast-Map z3-ast-map?)
  (#:opaque Z3-Ast z3-ast?)
  (#:opaque Z3-Stats z3-stats?)
  (#:opaque Z3-Ast-Vector z3-ast-vector?)
  (#:opaque Z3-Probe z3-probe?)
  (#:opaque Z3-Theory z3-theory?)
  (#:opaque Z3-Func-Interp z3-func-interp?)
  (#:opaque Z3-Goal z3-goal?)
  (#:opaque Z3-Func-Entry z3-func-entry?)
  (#:opaque Z3-Sort z3-sort?)
  (#:opaque Z3-Symbol z3-symbol?)
  (#:opaque Z3-Bool z3-bool?)
  (#:opaque Z3-Func-Decl z3-func-decl?)
  (#:opaque Z3-Optimize z3-optimize?)
  (#:opaque Z3-Model z3-model?)
  (#:opaque Z3-Config z3-config?)
  (#:opaque Z3-Pattern z3-pattern?)
  (#:opaque Z3-Apply-Result z3-apply-result?)
  (#:opaque Z3-Theory-Data z3-theory-data?)
  (#:opaque Z3-App z3-app?)
  (#:opaque Z3-Constructor-List z3-constructor-list?)
  (#:opaque Z3-Params z3-params?)
  (#:opaque Z3-String z3-string?)
  (#:opaque Z3-Tactic z3-tactic?)
  (#:opaque Z3-Rcf-Num z3-rcf-num?)
  (#:opaque Z3-Context z3-context?)
  (#:opaque Z3-Null z3-null?)
  (z3-null Z3-Null))
