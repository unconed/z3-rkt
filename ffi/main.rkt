#lang typed/racket/base

(require racket/match
         "types.rkt")

;; TODO: Hmm for some reason this makes it slower (slight, but measurable)
(begin
  (require typed/racket/unsafe)
  (define-syntax-rule (unsafe-require/typed/provide path [x t] ...)
    (begin
      (unsafe-require/typed path [x t] ...)
      (unsafe-provide x ...))))

(require/typed/provide "wrappers.rkt"
  [global-param-set! (Global-Param String → Void)]
  [global-param-get (Global-Param → String)]
  
  [del-config (Z3:Config → Void)]
  [set-param-value! (Z3:Config String String → Void)]
  [mk-context (Z3:Config → Z3:Context)]
  [del-context (Z3:Context → Void)]
  ;[update-param-value! (Z3:Context String String → Void)]
  [interrupt (Z3:Context → Void)]
  [z3-null Z3:Null]

  [mk-solver (Z3:Context → Z3:Solver)]
  [mk-simple-solver (Z3:Context → Z3:Solver)]
  [mk-solver-for-logic (Z3:Context Z3:Symbol → Z3:Solver)]
  [solver-get-help (Z3:Context Z3:Solver → String)]
  [solver-get-param-descrs (Z3:Context Z3:Solver → Z3:Param-Descrs)]
  [solver-set-params! (Z3:Context Z3:Solver Z3:Params → Void)]
  [solver-inc-ref! (Z3:Context Z3:Solver → Void)]
  [solver-dec-ref! (Z3:Context Z3:Solver → Void)]
  [solver-push! (Z3:Context Z3:Solver → Void)]
  [solver-pop! (Z3:Context Z3:Solver Nonnegative-Fixnum -> Void)]
  [solver-reset! (Z3:Context Z3:Solver → Void)]
  [solver-get-num-scopes (Z3:Context Z3:Solver → Nonnegative-Fixnum)]
  [solver-assert! (Z3:Context Z3:Solver Z3:Ast → Void)]
  [solver-assert-and-track! (Z3:Context Z3:Solver Z3:Ast Z3:Ast → Void)]
  [solver-get-assertions (Z3:Context Z3:Solver → Z3:Ast-Vector)]
  [solver-check (Z3:Context Z3:Solver → Z3:LBool)]
  [solver-check-assumptions (Z3:Context Z3:Solver (Listof Z3:Ast) → Z3:LBool)]
  [solver-get-model (Z3:Context Z3:Solver → Z3:Model)]
  [solver-get-proof (Z3:Context Z3:Solver → Z3:Ast)]
  [solver-get-unsat-core (Z3:Context Z3:Solver → Z3:Ast-Vector)]
  [solver-get-reason-unknown (Z3:Context Z3:Solver → String)]
  [solver-get-statistics (Z3:Context Z3:Solver → Z3:Stats)]
  [solver->string (Z3:Context Z3:Solver → String)]
  
  [mk-string-symbol (Z3:Context String → Z3:Symbol)]

  ;; Parameters
  [mk-params (Z3:Context → Z3:Params)]
  [params-inc-ref! (Z3:Context Z3:Params → Void)]
  [params-dec-ref! (Z3:Context Z3:Params → Void)]
  [params-set-bool! (Z3:Context Z3:Params Z3:Symbol Boolean → Void)]
  [params-set-uint! (Z3:Context Z3:Params Z3:Symbol Nonnegative-Fixnum → Void)]
  [params-set-double! (Z3:Context Z3:Params Z3:Symbol Inexact-Real → Void)]
  [params-set-symbol! (Z3:Context Z3:Params Z3:Symbol Z3:Symbol → Void)]
  [params->string (Z3:Context Z3:Params → String)]
  [params-validate! (Z3:Context Z3:Params Z3:Param-Descrs → Void)]

  ;; Parameter Descriptions
  [param-descrs-inc-ref! (Z3:Context Z3:Param-Descrs → Void)]
  [param-descrs-dec-ref! (Z3:Context Z3:Param-Descrs → Void)]
  [param-descrs-get-kind (Z3:Context Z3:Param-Descrs Z3:Symbol → Z3:Param-Kind)]
  [param-descrs-size (Z3:Context Z3:Param-Descrs → Nonnegative-Fixnum)]
  [param-descrs-get-name (Z3:Context Z3:Param-Descrs Nonnegative-Fixnum → Z3:Symbol)]
  [param-descrs->string (Z3:Context Z3:Param-Descrs → String)]

  ;; Sorts
  [mk-uninterpreted-sort (Z3:Context Z3:Symbol → Z3:Sort)]
  [mk-bool-sort (Z3:Context → Z3:Sort)]
  [mk-int-sort (Z3:Context → Z3:Sort)]
  [mk-real-sort (Z3:Context → Z3:Sort)]
  [mk-bv-sort (Z3:Context Nonnegative-Fixnum → Z3:Sort)]
  [mk-array-sort (Z3:Context Z3:Sort Z3:Sort → Z3:Sort)]
  [mk-list-sort (Z3:Context Z3:Symbol Z3:Sort → list-instance)]
  [mk-constructor
   (Z3:Context Z3:Symbol Z3:Symbol (Listof (List Z3:Symbol (U Z3:Null Z3:Sort) Nonnegative-Fixnum)) → Z3:Constructor)]
  [del-constructor (Z3:Context Z3:Constructor → Void)]
  [mk-datatype (Z3:Context Z3:Symbol (Listof Z3:Constructor) → Z3:Sort)]
  [mk-constructor-list (Z3:Context (Listof Z3:Constructor) → Z3:Constructor-List)]
  [del-constructor-list (Z3:Context Z3:Constructor-List → Void)]
  [mk-datatypes (Z3:Context (Listof (Pairof Z3:Symbol Z3:Constructor-List)) → (Listof Z3:Sort))]
  [query-constructor
   (Z3:Context Z3:Constructor Nonnegative-Fixnum →
               (Values Z3:Func-Decl Z3:Func-Decl (Listof Z3:Func-Decl)))]

  [mk-true (Z3:Context → Z3:Ast)]
  [mk-false (Z3:Context → Z3:Ast)]
  [mk-eq (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-distinct (Z3:Context Z3:Ast * → Z3:Ast)]

  ;; Boolean operations
  [mk-not (Z3:Context Z3:Ast → Z3:Ast)]
  [mk-ite (Z3:Context Z3:Ast Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-iff (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-implies (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-xor (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-and (Z3:Context Z3:Ast * → Z3:Ast)]
  [mk-or (Z3:Context Z3:Ast * → Z3:Ast)]

  ;; Arithmetic operations
  [mk-add (Z3:Context Z3:Ast * → Z3:Ast)]
  [mk-mul (Z3:Context Z3:Ast * → Z3:Ast)]
  [mk-sub (Z3:Context Z3:Ast * → Z3:Ast)]
  [mk-div (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-mod (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-rem (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-power (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-is-int (Z3:Context Z3:Ast → Z3:Ast)]
  [mk-int2real (Z3:Context Z3:Ast → Z3:Ast)]

  ;; Comparisons
  [mk-lt (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-le (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-gt (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-ge (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]

  ;; Numerals
  [mk-numeral (Z3:Context String Z3:Sort → Z3:Ast)]

  ;; Uninterpreted constants, functions and applications
  [mk-func-decl (Z3:Context Z3:Symbol (Listof Z3:Sort) Z3:Sort → Z3:Func-Decl)]
  [mk-app (Z3:Context Z3:Func-Decl Z3:Ast * → Z3:Ast)]
  [mk-const (Z3:Context Z3:Symbol Z3:Sort → Z3:App)]
  [mk-fresh-func-decl (Z3:Context String (Listof Z3:Sort) Z3:Sort → Z3:Func-Decl)]
  [mk-fresh-const (Z3:Context String Z3:Sort → Z3:App)]

  ;; Arrays
  [mk-select (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-store (Z3:Context Z3:Ast Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-const-array (Z3:Context Z3:Sort Z3:Ast → Z3:Ast)]
  [mk-map (Z3:Context Z3:Func-Decl Z3:Ast * → Z3:Ast)]
  [mk-array-default (Z3:Context Z3:Ast → Z3:Ast)]

  ;; Sets
  [mk-set-sort (Z3:Context Z3:Sort → Z3:Sort)]
  [mk-empty-set (Z3:Context Z3:Sort → Z3:Ast)]
  [mk-full-set (Z3:Context Z3:Sort → Z3:Ast)]
  [mk-set-add (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-set-del (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-set-union (Z3:Context Z3:Ast * → Z3:Ast)]
  [mk-set-intersect (Z3:Context Z3:Ast * → Z3:Ast)]
  [mk-set-difference (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-set-complement (Z3:Context Z3:Ast → Z3:Ast)]
  [mk-set-member (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-set-subset (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]

  ;; Quantifiers
  [mk-pattern (Z3:Context Z3:Ast Z3:Ast * → Z3:Pattern)]
  [mk-bound (Z3:Context Nonnegative-Fixnum Z3:Sort → Z3:Ast)]
  [mk-forall
   (Z3:Context Nonnegative-Fixnum (Listof Z3:Pattern) (Listof (Pairof Z3:Symbol Z3:Sort)) Z3:Ast → Z3:Ast)]
  [mk-exists
   (Z3:Context Nonnegative-Fixnum (Listof Z3:Pattern) (Listof (Pairof Z3:Symbol Z3:Sort)) Z3:Ast → Z3:Ast)]
  [mk-quantifier
   (Z3:Context Boolean Nonnegative-Fixnum (Listof Z3:Pattern) (Listof (Pairof Z3:Symbol Z3:Sort)) Z3:Ast → Z3:Ast)]
  [mk-forall-const
   (Z3:Context Nonnegative-Fixnum (Listof Z3:App) (Listof Z3:Pattern) Z3:Ast → Z3:Ast)]
  [mk-exists-const
   (Z3:Context Nonnegative-Fixnum (Listof Z3:App) (Listof Z3:Pattern) Z3:Ast → Z3:Ast)]
  [mk-quantifier-const
   (Z3:Context Boolean Nonnegative-Fixnum (Listof Z3:App) (Listof Z3:Pattern) Z3:Ast → Z3:Ast)]

  ;; Accessors
  [get-symbol-string (Z3:Context Z3:Symbol → String)]
  [get-decl-name (Z3:Context Z3:Func-Decl → Z3:Symbol)]
  [get-domain-size (Z3:Context Z3:Func-Decl → Nonnegative-Fixnum)]
  [get-arity (Z3:Context Z3:Func-Decl → Nonnegative-Fixnum)]
  [get-domain (Z3:Context Z3:Func-Decl Nonnegative-Fixnum → Z3:Sort)]
  [get-range (Z3:Context Z3:Func-Decl → Z3:Sort)]
  [app->ast (Z3:Context Z3:App → Z3:Ast)]
  [get-app-decl (Z3:Context Z3:App → Z3:Func-Decl)]
  [get-app-num-args (Z3:Context Z3:App → Nonnegative-Fixnum)]
  [get-app-arg (Z3:Context Z3:App Nonnegative-Fixnum → Z3:Ast)]
  [get-sort (Z3:Context Z3:Ast → Z3:Sort)]
  [get-bool-value (Z3:Context Z3:Ast → Z3:LBool)]
  [get-ast-kind (Z3:Context Z3:Ast → Z3:Ast-Kind)]
  [is-numeral-ast? (Z3:Context Z3:Ast → Boolean)]
  [to-app (Z3:Context Z3:Ast → Z3:App)]
  [get-numeral-string (Z3:Context Z3:Ast → String)]

  ;; String conversion
  [set-ast-print-mode! (Z3:Context Z3:Ast-Print-Mode → Void)]
  [ast->string (Z3:Context Z3:Ast → String)]
  [pattern->string (Z3:Context Z3:Pattern → String)]
  [sort->string (Z3:Context Z3:Sort → String)]
  [func-decl->string (Z3:Context Z3:Func-Decl → String)]
  [model->string (Z3:Context Z3:Model → String)]

  ;; Parser interface
  [parse-smtlib2-string
   (Z3:Context String (Listof (Pairof Z3:Symbol Z3:Sort)) (Listof (Pairof Z3:Symbol Z3:Func-Decl)) → Z3:Ast)]
  [parse-smtlib2-file
   (Z3:Context String (Listof (Pairof Z3:Symbol Z3:Sort)) (Listof (Pairof Z3:Symbol Z3:Func-Decl)) → Z3:Ast)]
  [parse-smtlib-string!
   (Z3:Context String (Listof (Pairof Z3:Symbol Z3:Sort)) (Listof (Pairof Z3:Symbol Z3:Func-Decl)) → Void)]
  [parse-smtlib-file!
   (Z3:Context String (Listof (Pairof Z3:Symbol Z3:Sort)) (Listof (Pairof Z3:Symbol Z3:Func-Decl)) → Void)]
  [get-smtlib-num-formulas (Z3:Context → Nonnegative-Fixnum)]
  [get-smtlib-formula (Z3:Context Nonnegative-Fixnum → Z3:Ast)]
  [get-smtlib-num-assumptions (Z3:Context → Nonnegative-Fixnum)]
  [get-smtlib-assumption (Z3:Context Nonnegative-Fixnum → Z3:Ast)]
  [get-smtlib-num-decls (Z3:Context → Nonnegative-Fixnum)]
  [get-smtlib-decl (Z3:Context Nonnegative-Fixnum → Z3:Func-Decl)]
  [get-smtlib-num-sorts (Z3:Context → Nonnegative-Fixnum)]
  [get-smtlib-sort (Z3:Context Nonnegative-Fixnum → Z3:Sort)]
  [get-smtlib-error (Z3:Context → String)]

  ;; error handling functions
  [get-error-code (Z3:Context → Z3:Error-Code)]
  [get-error-msg (Z3:Error-Code → String)]

  ;; Model
  [model-inc-ref! (Z3:Context Z3:Model → Void)]
  [model-dec-ref! (Z3:Context Z3:Model → Void)]
  [model-eval (Z3:Context Z3:Model Z3:Ast Boolean → (Option Z3:Ast))]
  [model-get-const-interp (Z3:Context Z3:Model Z3:Func-Decl → Z3:Ast)]
  [model-has-interp? (Z3:Context Z3:Model Z3:Func-Decl → Boolean)]
  [model-get-func-interp (Z3:Context Z3:Model Z3:Func-Decl → (Option Z3:Func-Interp))]
  [model-get-num-consts (Z3:Context Z3:Model → Nonnegative-Fixnum)]
  [model-get-const-decl (Z3:Context Z3:Model Nonnegative-Fixnum → Z3:Func-Decl)]
  [model-get-num-funcs (Z3:Context Z3:Model → Nonnegative-Fixnum)]
  [model-get-func-decl (Z3:Context Z3:Model Nonnegative-Fixnum → Z3:Func-Decl)]
  [model-get-num-sorts (Z3:Context Z3:Model → Nonnegative-Fixnum)]
  [model-get-sort (Z3:Context Z3:Model Nonnegative-Fixnum → Z3:Sort)]
  [model-get-sort-universe (Z3:Context Z3:Model Z3:Sort → Z3:Ast-Vector)]
  [is-as-array? (Z3:Context Z3:Ast → Boolean)]
  [get-as-array-func-decl (Z3:Context Z3:Ast → Z3:Func-Decl)]
  [func-interp-inc-ref! (Z3:Context Z3:Func-Interp → Void)]
  [func-interp-dec-ref! (Z3:Context Z3:Func-Interp → Void)]
  [func-interp-get-num-entries (Z3:Context Z3:Func-Interp → Nonnegative-Fixnum)]
  [func-interp-get-entry (Z3:Context Z3:Func-Interp Nonnegative-Fixnum → Z3:Func-Entry)]
  [func-interp-get-else (Z3:Context Z3:Func-Interp → Z3:Ast)]
  [func-interp-get-arity (Z3:Context Z3:Func-Interp → Nonnegative-Fixnum)]
  [func-entry-inc-ref! (Z3:Context Z3:Func-Entry → Void)]
  [func-entry-dec-ref! (Z3:Context Z3:Func-Entry → Void)]
  [func-entry-get-value (Z3:Context Z3:Func-Entry → Z3:Ast)]
  [func-entry-get-num-args (Z3:Context Z3:Func-Entry → Nonnegative-Fixnum)]
  [func-entry-get-arg (Z3:Context Z3:Func-Entry Nonnegative-Fixnum → Z3:Ast)]

  ;; Interaction logging
  [open-log (String → Boolean)]
  [append-log! (String → Void)]
  [close-log! (→ Boolean)]
  [toggle-warning-messages! (Boolean → Void)]

  ;; Statistics
  [stats->string (Z3:Context Z3:Stats → String)]
  [stats-inc-ref! (Z3:Context Z3:Stats → Void)]
  [stats-dec-ref! (Z3:Context Z3:Stats → Void)]
  [stats-size (Z3:Context Z3:Stats → Nonnegative-Fixnum)]
  [stats-get-key (Z3:Context Z3:Stats Nonnegative-Fixnum → String)]
  [stats-is-uint? (Z3:Context Z3:Stats Nonnegative-Fixnum → Boolean)]
  [stats-is-double? (Z3:Context Z3:Stats Nonnegative-Fixnum → Boolean)]
  [stats-get-uint-value (Z3:Context Z3:Stats Nonnegative-Fixnum → Nonnegative-Fixnum)]
  [stats-get-double-value (Z3:Context Z3:Stats Nonnegative-Fixnum → Inexact-Real)]

  ;; AST Vectors
  [mk-ast-vector (Z3:Context → Z3:Ast-Vector)]
  [ast-vector-inc-ref! (Z3:Context Z3:Ast-Vector → Void)]
  [ast-vector-dec-ref! (Z3:Context Z3:Ast-Vector → Void)]
  [ast-vector-size (Z3:Context Z3:Ast-Vector → Nonnegative-Fixnum)]
  [ast-vector-get (Z3:Context Z3:Ast-Vector Nonnegative-Fixnum → Z3:Ast)]
  [ast-vector-set! (Z3:Context Z3:Ast-Vector Nonnegative-Fixnum Z3:Ast → Void)]
  [ast-vector-resize! (Z3:Context Z3:Ast-Vector Nonnegative-Fixnum → Void)]
  [ast-vector-push! (Z3:Context Z3:Ast-Vector Z3:Ast → Void)]
  [ast-vector-translate (Z3:Context Z3:Ast-Vector Z3:Context → Z3:Ast-Vector)]
  [ast-vector->string (Z3:Context Z3:Ast-Vector → String)]

  ;; Miscellaneous
  [get-version
   (→ (Values Nonnegative-Fixnum Nonnegative-Fixnum Nonnegative-Fixnum Nonnegative-Fixnum))]
  [enable-trace! (String → Void)]
  [disable-trace! (String → Void)]
  [reset-memory! (→ Void)]
  [finalize-memory! (→ Void)]
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Enhanced interface for low-level functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require/typed racket/base
  [(make-keyword-procedure
    make-config-keyword-procedure)
   (((Listof Keyword) (Listof (U Boolean Nonnegative-Fixnum String)) → Z3:Config) →
    ([]
     [#:proof? Boolean
      #:debug-ref-count? Boolean
      #:trace? Boolean
      #:trace-file-name String
      #:timeout Nonnegative-Fixnum
      #:rlimit Nonnegative-Fixnum
      #:type-check? Boolean
      #:well-sorted-check? Boolean
      #:auto-config? Boolean
      #:model? Boolean
      #:model-validate? Boolean
      #:unsat-core? Boolean]
     . ->* . Z3:Config))])

(require/typed "wrappers.rkt"
  [(mk-config raw:mk-config) (→ Z3:Config)])

(define mk-config
  (let ()

    (: keyword-arg->_z3-param :
       Keyword (U Boolean Nonnegative-Fixnum String) → (Values String String))
    (define (keyword-arg->_z3-param kw kw-arg)
      (define kw-str (assert (regexp-replaces (keyword->string kw)
                                              '((#rx"-" "_") (#rx"\\?$" "")))
                             string?))
      (define kw-arg-str (match kw-arg
                           [#t "true"]
                           [#f "false"]
                           [(? integer?) (number->string kw-arg)]
                           [(? string?) kw-arg]))
      (values kw-str kw-arg-str))

    (make-config-keyword-procedure
     (λ (kws kw-args)
       (define cfg (raw:mk-config))
       (for ([kw kws] [kw-arg kw-args])
         (define-values (k v) (keyword-arg->_z3-param kw kw-arg))
         (set-param-value! cfg k v))
       cfg))))
(provide mk-config)

(provide (all-from-out "types.rkt"))
