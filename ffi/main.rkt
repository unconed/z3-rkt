#lang typed/racket/base

(require racket/match
         "types.rkt")

(require/typed/provide "wrappers.rkt"
  [toggle-warning-messages! (Boolean → Void)]
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
  [solver-inc-ref! (Z3:Context Z3:Solver → Void)]
  [solver-dec-ref! (Z3:Context Z3:Solver → Void)]
  [solver-push! (Z3:Context Z3:Solver → Void)]
  [solver-pop! (Z3:Context Z3:Solver Nonnegative-Fixnum -> Void)]
  [solver-reset! (Z3:Context Z3:Solver → Void)]
  [solver-assert! (Z3:Context Z3:Solver Z3:Ast → Void)]
  [solver-assert-and-track! (Z3:Context Z3:Solver Z3:Ast Z3:Ast → Void)]
  [solver-check (Z3:Context Z3:Solver → Z3:LBool)]
  [solver-get-model (Z3:Context Z3:Solver → Z3:Model)]
  [solver-get-reason-unknown (Z3:Context Z3:Solver → String)]
  [solver-get-statistics (Z3:Context Z3:Solver → Z3:Stats)]
  [solver-to-string (Z3:Context Z3:Solver → String)]
  
  [mk-string-symbol (Z3:Context String → Z3:Symbol)]
  [mk-uninterpreted-sort (Z3:Context Z3:Symbol → Z3:Sort)]
  [mk-bool-sort (Z3:Context → Z3:Sort)]
  [mk-int-sort (Z3:Context → Z3:Sort)]
  [mk-real-sort (Z3:Context → Z3:Sort)]
  [mk-bv-sort (Z3:Context Nonnegative-Fixnum → Z3:Sort)]
  [mk-array-sort (Z3:Context Z3:Sort Z3:Sort → Z3:Sort)]
  [mk-list-sort (Z3:Context Z3:Symbol Z3:Sort → list-instance)]
  [mk-true (Z3:Context → Z3:Ast)]
  [mk-false (Z3:Context → Z3:Ast)]
  [mk-eq (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-distinct (Z3:Context Z3:Ast * → Z3:Ast)]
  [mk-pattern (Z3:Context Z3:Ast Z3:Ast * → Z3:Pattern)]

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

  ;; Comparisons
  [mk-lt (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-le (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-gt (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-ge (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]

  ;; Numerals
  [mk-numeral (Z3:Context String Z3:Sort → Z3:Ast)]

  ;; Uninterpreted constants, functions and applications
  [mk-fresh-func-decl (Z3:Context String (Listof Z3:Sort) Z3:Sort → Z3:Func-Decl)]
  [mk-app (Z3:Context Z3:Func-Decl Z3:Ast * → Z3:Ast)]
  [mk-fresh-const (Z3:Context String Z3:Sort → Z3:App)]

  ;; Array operations
  [mk-select (Z3:Context Z3:Ast Z3:Ast → Z3:Ast)]
  [mk-store (Z3:Context Z3:Ast Z3:Ast Z3:Ast → Z3:Ast)]

  ;; Complex types
  [mk-constructor
   (Z3:Context Z3:Symbol Z3:Symbol (Listof (List Z3:Symbol (U Z3:Null Z3:Sort) Nonnegative-Fixnum)) → Z3:Constructor)]

  [query-constructor
   (Z3:Context Z3:Constructor Nonnegative-Fixnum →
               (Values Z3:Func-Decl Z3:Func-Decl (Listof Z3:Func-Decl)))]

  [mk-datatype (Z3:Context Z3:Symbol (Listof Z3:Constructor) → Z3:Sort)]

  ;; Quantifiers
  [mk-forall-const
   (Z3:Context Nonnegative-Fixnum (Listof Z3:App) (Listof Z3:Pattern) Z3:Ast → Z3:Ast)]
  [mk-exists-const
   (Z3:Context Nonnegative-Fixnum (Listof Z3:App) (Listof Z3:Pattern) Z3:Ast → Z3:Ast)]

  ;; → string functions
  [ast-to-string (Z3:Context Z3:Ast → String)]
  [model-to-string (Z3:Context Z3:Model → String)]
  [sort-to-string (Z3:Context Z3:Sort → String)]
  [func-decl-to-string (Z3:Context Z3:Func-Decl → String)]

  ;; error handling functions
  [get-error-code (Z3:Context → Z3:Error-Code)]
  [get-error-msg (Z3:Error-Code → String)]

  ;; FIXME tmp hacks
  [z3-get-sort (Z3:Context Z3:Ast → Z3:Sort)]

  [get-ast-kind (Z3:Context Z3:Ast → Z3:Ast-Kind)]
  [get-numeral-string (Z3:Context Z3:Ast → String)]
  [to-app (Z3:Context Z3:Ast → Z3:App)]
  [get-app-num-args (Z3:Context Z3:App → Nonnegative-Fixnum)]
  [app-to-ast (Z3:Context Z3:App → Z3:Ast)]
  [get-app-decl (Z3:Context Z3:App → Z3:Func-Decl)]

  ;; Statistics
  [stats-to-string (Z3:Context Z3:Stats → String)]
  [stats-inc-ref! (Z3:Context Z3:Stats → Void)]
  [stats-dec-ref! (Z3:Context Z3:Stats → Void)]
  [stats-size (Z3:Context Z3:Stats → Nonnegative-Fixnum)]
  [stats-get-key (Z3:Context Z3:Stats Nonnegative-Fixnum → String)]
  [stats-is-uint? (Z3:Context Z3:Stats Nonnegative-Fixnum → Boolean)]
  [stats-is-double? (Z3:Context Z3:Stats Nonnegative-Fixnum → Boolean)]
  [stats-get-uint-value (Z3:Context Z3:Stats Nonnegative-Fixnum → Nonnegative-Fixnum)]
  [stats-get-double-value (Z3:Context Z3:Stats Nonnegative-Fixnum → Inexact-Real)]
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Enhanced interface for low-level functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require/typed racket/base
  [(make-keyword-procedure
    make-config-keyword-procedure)
   (((Listof Keyword) (Listof (U Boolean Integer String)) → Z3:Config) →
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

    (: keyword-arg->_z3-param : Keyword (U Boolean Integer String) → (Values String String))
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
