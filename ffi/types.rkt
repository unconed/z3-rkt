#lang typed/racket/base

(provide (all-defined-out))

(define-type Z3:LBool (U 'false 'undef 'true))
(define-type Z3:Sat-LBool (U 'unsat 'unknown 'sat))
(define-type Z3:Ast-Kind (U 'numeral 'app 'var 'quantifier 'unknown))
(define-type Z3:Error-Code (U 'ok 'sort-error 'iob 'invalid-arg 'parser-error
                              'no-parser 'invalid-pattern 'memout-fail
                              'file-access-error 'invalid-usage
                              'internal-fatal 'dec-ref-error))
(define-type Global-Param
  (U "auto_config"
     "debug_ref_count"
     "dump_models"
     "memory_high_watermark"
     "memory_max_alloc_count"
     "memory_max_size"
     "model"
     "model_validate"
     "proof"
     "rlimit"
     "smtlib2_compliant"
     "timeout"
     "trace"
     "trace_file_name"
     "type_check"
     "unsat_core"
     "verbose"
     "warning"
     "well_sorted_check"))

(require/typed/provide "wrappers.rkt"
  [#:opaque Z3:Config  z3-config?]
  [#:opaque Z3:Context z3-context?]
  [#:opaque Z3:Solver      z3-solver?]
  [#:opaque Z3:Func-Decl   z3-func-decl?]
  [#:opaque Z3:Symbol      z3-symbol?]
  [#:opaque Z3:Ast         z3-ast?]
  [#:opaque Z3:Sort        z3-sort?]
  [#:opaque Z3:App         z3-app?]
  [#:opaque Z3:Constructor z3-constructor?]
  [#:opaque Z3:Pattern     z3-pattern?]
  [#:opaque Z3:Model       z3-model?]
  [#:opaque Z3:Stats       z3-stats?]
  [#:opaque Z3:Ast-Vector  z3-ast-vector?]
  [#:opaque Z3:Null        z3-null?]
  [#:struct list-instance ([sort : Z3:Sort]
                           [nil : Z3:Func-Decl]
                           [is-nil : Z3:Func-Decl]
                           [cons : Z3:Func-Decl]
                           [is-cons : Z3:Func-Decl]
                           [head : Z3:Func-Decl]
                           [tail : Z3:Func-Decl])])

(define-type Z3:Func (Expr * → Z3:Ast))
(define-type Expr (U Z3:Ast Z3:App Real Symbol))
(define-type Sort-Expr (U Z3:Sort Symbol))
