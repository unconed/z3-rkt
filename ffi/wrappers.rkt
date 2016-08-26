#lang racket/base

(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         racket/match
         ffi/unsafe
         ffi/unsafe/alloc
         racket/runtime-path)
(provide (struct-out list-instance))

(define-runtime-path libz3-path
  (case (system-type 'os)
    [(unix) "libz3.so"]
    [(windows) "z3.dll"]
    [(macosx) "libz3.dylib"]))

(define libz3
  (let ([libz3-without-suffix (path-replace-extension libz3-path "")])
    (ffi-lib libz3-without-suffix)))

(define-cpointer-type _z3-config)  (provide z3-config?)
(define-cpointer-type _z3-context) (provide z3-context?)

;; Indicates an instance of a List (e.g. List Int) .
(struct list-instance (sort nil is-nil cons is-cons head tail) #:transparent)

(define-syntax defz3
  (syntax-rules (:)
    [(_ x : t ...)
     (defz3 x #:wrapper values : t ...)]
    [(_ x #:wrapper w : t ...)
     (begin
       (define x
         (let* ([c-name (regexp-replaces (format "Z3_~a" 'x) '((#rx"-" "_")
                                                               (#rx"!$" "")
                                                               (#rx"\\?$" "")))]
                [func (get-ffi-obj c-name libz3 (_fun t ...))])
           (w func)))
       (provide x))]))

;; Helper macro to define n-ary AST functions
(define-syntax define-nary
  (syntax-rules (: ->)
    [(_ fn : argtype -> rettype)
     (defz3 fn : (ctx . args) ::
       (ctx : _z3-context)
       (_uint = (length args))
       (args : (_list i argtype)) -> rettype)]))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;; Low-level bindings
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-cpointer-type _z3-solver     ) (provide z3-solver?)
(define-cpointer-type _z3-symbol     ) (provide z3-symbol?)
(define-cpointer-type _z3-ast        ) (provide z3-ast?)
(define-cpointer-type _z3-sort       ) (provide z3-sort?)
(define-cpointer-type _z3-app        ) (provide z3-app?)
(define-cpointer-type _z3-func-decl  ) (provide z3-func-decl?)
(define-cpointer-type _z3-constructor) (provide z3-constructor?)
(define-cpointer-type _z3-pattern    ) (provide z3-pattern?)
(define-cpointer-type _z3-model      ) (provide z3-model?)
(define-cpointer-type _z3-stats      ) (provide z3-stats?)
(define z3-null #f)
(define z3-null? not)
(provide z3-null z3-null?)

;; Enumerations
(define _z3-lbool (_enum '(false = -1 undef true) _int32))
(define _z3-sat-lbool (_enum '(unsat = -1 unknown sat) _int32))
(define _z3-ast-kind (_enum '(numeral app var quantifier unknown = 1000) _int32))
(define _z3-error-code (_enum '(ok sort-error iob invalid-arg parser-error
                                   no-parser invalid-pattern memout-fail
                                   file-access-error invalid-usage
                                   internal-fatal dec-ref-error) _int32))

(define _z3-error-handler (_fun #:keep #t _int -> _void))

(defz3 toggle-warning-messages! : _bool -> _void)

;; Deallocators
(defz3 del-config  : _z3-config  -> _void)
(defz3 del-context : _z3-context -> _void)

(defz3 global-param-set! : _string _string -> _void)
(defz3 global-param-get : _string
  (val : (_ptr o _string))
  -> (ok? : _bool)
  -> (and ok? val))

(defz3 mk-config : -> _z3-config)
(defz3 set-param-value! : _z3-config _string _string -> _void)

(defz3 mk-context : _z3-config -> _z3-context)
;(defz3 update-param-value! : _z3-context _string _string -> _void) ; get Z3 Exception when used
(defz3 interrupt : _z3-context -> _void)

;; Solver API
(defz3 mk-solver : _z3-context -> _z3-solver)
(defz3 mk-simple-solver : _z3-context -> _z3-solver)
(defz3 mk-solver-for-logic : _z3-context _z3-symbol -> _z3-solver)
; TODO: mk-solver-from-tactic
(defz3 solver-get-help : _z3-context _z3-solver -> _string)
; TODO: solver-get-param-descrs
; TODO: solver-set-params
(defz3 solver-inc-ref! : _z3-context _z3-solver -> _void)
(defz3 solver-dec-ref! : _z3-context _z3-solver -> _void)
(defz3 solver-push! : _z3-context _z3-solver -> _void)
(defz3 solver-pop! : _z3-context _z3-solver _uint -> _void)
(defz3 solver-reset! : _z3-context _z3-solver -> _void)
; TODO: solver-get-num-scopes
(defz3 solver-assert! : _z3-context _z3-solver _z3-ast -> _void)
(defz3 solver-assert-and-track! : _z3-context _z3-solver _z3-ast _z3-ast -> _void)
; TODO: solver-get-assertions
(defz3 solver-check : _z3-context _z3-solver -> _z3-lbool)
; TODO: solver-check-assumptions
(defz3 solver-get-model : _z3-context _z3-solver -> _z3-model)
; TODO: solver-get-proof, solver-get-unsat-core
(defz3 solver-get-reason-unknown : _z3-context _z3-solver -> _string)
(defz3 solver-get-statistics : _z3-context _z3-solver -> _z3-stats)
(defz3 solver-to-string : _z3-context _z3-solver -> _string)

(defz3 mk-string-symbol : _z3-context _string -> _z3-symbol)
(defz3 mk-uninterpreted-sort : _z3-context _z3-symbol -> _z3-sort)
(defz3 mk-bool-sort : _z3-context -> _z3-sort)
(defz3 mk-int-sort : _z3-context -> _z3-sort)
(defz3 mk-real-sort : _z3-context -> _z3-sort)
(defz3 mk-bv-sort : _z3-context _uint -> _z3-sort)
(defz3 mk-array-sort : _z3-context _z3-sort _z3-sort -> _z3-sort)

(defz3 mk-list-sort : _z3-context _z3-symbol _z3-sort
  (nil-decl : (_ptr o _z3-func-decl))
  (is-nil-decl : (_ptr o _z3-func-decl))
  (cons-decl : (_ptr o _z3-func-decl))
  (is-cons-decl : (_ptr o _z3-func-decl))
  (head-decl : (_ptr o _z3-func-decl))
  (tail-decl : (_ptr o _z3-func-decl))
  -> (res : _z3-sort) ->
  (list-instance res
                 nil-decl
                 is-nil-decl
                 cons-decl
                 is-cons-decl
                 head-decl
                 tail-decl))

(defz3 mk-true : _z3-context -> _z3-ast)
(defz3 mk-false : _z3-context -> _z3-ast)
(defz3 mk-eq : _z3-context _z3-ast _z3-ast -> _z3-ast)

(define-nary mk-distinct : _z3-ast -> _z3-ast)

(define-nary mk-pattern : _z3-ast -> _z3-pattern)

;; Boolean operations
(defz3 mk-not : _z3-context _z3-ast -> _z3-ast)
(defz3 mk-ite : _z3-context _z3-ast _z3-ast _z3-ast -> _z3-ast)
(defz3 mk-iff : _z3-context _z3-ast _z3-ast -> _z3-ast)
(defz3 mk-implies : _z3-context _z3-ast _z3-ast -> _z3-ast)
(defz3 mk-xor : _z3-context _z3-ast _z3-ast -> _z3-ast)
(define-nary mk-and : _z3-ast -> _z3-ast)
(define-nary mk-or : _z3-ast -> _z3-ast)

;; Arithmetic operations
(define-nary mk-add : _z3-ast -> _z3-ast)
(define-nary mk-mul : _z3-ast -> _z3-ast)
(define-nary mk-sub : _z3-ast -> _z3-ast)
(defz3 mk-div : _z3-context _z3-ast _z3-ast -> _z3-ast)
(defz3 mk-mod : _z3-context _z3-ast _z3-ast -> _z3-ast)
(defz3 mk-rem : _z3-context _z3-ast _z3-ast -> _z3-ast)
(defz3 mk-power : _z3-context _z3-ast _z3-ast -> _z3-ast)
(defz3 mk-is-int : _z3-context _z3-ast -> _z3-ast)
(defz3 mk-int2real : _z3-context _z3-ast -> _z3-ast)

;; Comparisons
(defz3 mk-lt : _z3-context _z3-ast _z3-ast -> _z3-ast)
(defz3 mk-le : _z3-context _z3-ast _z3-ast -> _z3-ast)
(defz3 mk-gt : _z3-context _z3-ast _z3-ast -> _z3-ast)
(defz3 mk-ge : _z3-context _z3-ast _z3-ast -> _z3-ast)

;; Numerals
(defz3 mk-numeral : _z3-context _string _z3-sort -> _z3-ast)

;; Uninterpreted constants, functions and applications
(defz3 mk-fresh-func-decl : (ctx prefix domain range) ::
  (ctx : _z3-context)
  (prefix : _string)
  (_uint = (length domain))
  (domain : (_list i _z3-sort))
  (range : _z3-sort)
  -> _z3-func-decl)

(defz3 mk-app : (ctx d . args) ::
  (ctx : _z3-context)
  (d : _z3-func-decl)
  (_uint = (length args))
  (args : (_list i _z3-ast)) -> _z3-ast)

(defz3 mk-fresh-const : _z3-context _string _z3-sort -> _z3-app)

;; Array operations
(defz3 mk-select : _z3-context _z3-ast _z3-ast -> _z3-ast)
(defz3 mk-store : _z3-context _z3-ast _z3-ast _z3-ast -> _z3-ast)

;; Complex types
(defz3 mk-constructor :
  (ctx name recognizer names-sorts-refs) ::
  (ctx         : _z3-context)
  (name        : _z3-symbol)
  (recognizer  : _z3-symbol)
  (num-fields  : _uint = (length names-sorts-refs))
  (field-names : (_list i _z3-symbol) = (map car names-sorts-refs))
  (sorts       : (_list i _z3-sort/null) = (map cadr names-sorts-refs))
  (sort-refs   : (_list i _uint) = (map caddr names-sorts-refs))
  -> _z3-constructor)

(defz3 query-constructor :
  (ctx constructor num-fields) ::
  (ctx            : _z3-context)
  (constructor    : _z3-constructor)
  (num-fields     : _uint)
  (constructor-fn : (_ptr o _z3-func-decl))
  (tester-fn      : (_ptr o _z3-func-decl))
  (accessor-fns   : (_list o _z3-func-decl num-fields))
  -> _void ->
  (values constructor-fn tester-fn accessor-fns))

(defz3 mk-datatype :
  (ctx name constructors) ::
  (ctx : _z3-context)
  (name : _z3-symbol)
  (_uint = (length constructors))
  (constructors : (_list i _z3-constructor))
  -> _z3-sort)

;; Quantifiers
(defz3 mk-forall-const :
  (ctx weight bound-consts patterns body) ::
  (ctx : _z3-context)
  (weight : _uint)
  (_uint = (length bound-consts))
  (bound-consts : (_list i _z3-app))
  (_uint = (length patterns))
  (patterns : (_list i _z3-pattern))
  (body : _z3-ast)
  -> _z3-ast)
(defz3 mk-exists-const :
  (ctx weight bound-consts patterns body) ::
  (ctx : _z3-context)
  (weight : _uint)
  (_uint = (length bound-consts))
  (bound-consts : (_list i _z3-app))
  (_uint = (length patterns))
  (patterns : (_list i _z3-pattern))
  (body : _z3-ast)
  -> _z3-ast)

;; -> string functions
(defz3 ast-to-string : _z3-context _z3-ast -> _string)
(defz3 model-to-string : _z3-context _z3-model -> _string)
(defz3 sort-to-string : _z3-context _z3-sort -> _string)
(defz3 func-decl-to-string : _z3-context _z3-func-decl -> _string)

;; error handling functions
(defz3 get-error-code : _z3-context -> _z3-error-code)
(defz3 get-error-msg : _z3-error-code -> _string)

;; TODO tmp hacks
(begin
  (define z3-get-sort
    (get-ffi-obj "Z3_get_sort" libz3 (_fun _z3-context _z3-ast -> _z3-sort)))
  (provide z3-get-sort))

(defz3 get-ast-kind : _z3-context _z3-ast -> _z3-ast-kind)
(defz3 get-numeral-string : _z3-context _z3-ast -> _string)
(defz3 to-app : _z3-context _z3-ast -> _z3-app)
(defz3 get-app-num-args : _z3-context _z3-app -> _uint)
(defz3 app-to-ast : _z3-context _z3-app -> _z3-ast)
(defz3 get-app-decl : _z3-context _z3-app -> _z3-func-decl)

;; Model
(defz3 model-inc-ref! : _z3-context _z3-model -> _void)
(defz3 model-dec-ref! : _z3-context _z3-model -> _void)
(defz3 model-eval : _z3-context _z3-model _z3-ast _bool (res : (_ptr o _z3-ast))
  -> (ok? : _bool)
  -> (and ok? res))
(defz3 model-get-const-decl : _z3-context _z3-model _uint -> _z3-func-decl)
(defz3 model-get-const-interp : _z3-context _z3-model _z3-func-decl -> _z3-ast)
(defz3 model-get-func-decl : _z3-context _z3-model _uint -> _z3-func-decl)
(defz3 model-get-func-interp : _z3-context _z3-model _z3-func-decl -> _z3-func-decl/null)
(defz3 model-get-num-consts : _z3-context _z3-model -> _uint)
(defz3 model-get-num-funcs : _z3-context _z3-model -> _uint)
(defz3 model-get-num-sorts : _z3-context _z3-model -> _uint)
(defz3 model-get-sort : _z3-context _z3-model _uint -> _z3-sort)
;; TODO model-get-sort-universe
(defz3 model-has-interp : _z3-context _z3-model _z3-func-decl -> _bool)
;; TODO model-to-string


;; Statistics
(defz3 stats-to-string : _z3-context _z3-stats -> _string)
(defz3 stats-inc-ref! : _z3-context _z3-stats -> _void)
(defz3 stats-dec-ref! : _z3-context _z3-stats -> _void)
(defz3 stats-size : _z3-context _z3-stats -> _uint)
(defz3 stats-get-key : _z3-context _z3-stats _uint -> _string)
(defz3 stats-is-uint? : _z3-context _z3-stats _uint -> _bool)
(defz3 stats-is-double? : _z3-context _z3-stats _uint -> _bool)
(defz3 stats-get-uint-value : _z3-context _z3-stats _uint -> _uint)
(defz3 stats-get-double-value : _z3-context _z3-stats _uint -> _double)
