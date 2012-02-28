#lang racket

(require "api.rkt")
(require "defs.rkt")

; This must be parameterized every time any syntax is used
(define ctx (make-parameter #f))
(define (current-context) (ctx))

(define ctx-namespace (make-parameter #f))
(define (get-value id)
  (namespace-variable-value id #t #f (ctx-namespace)))
(define (set-value id v)
  (namespace-set-variable-value! id v #t (ctx-namespace)))

;; A symbol table for sorts
(define ctx-sort-table (make-parameter #f))
(define (get-sort id)
  (hash-ref (ctx-sort-table) id))
(define (new-sort id v)
  (if (not (hash-ref (ctx-sort-table) id #f))
      (hash-set! (ctx-sort-table) id v)
      (raise (make-exn:fail "Defining a pre-existing sort!"))))

;; A complex sort (e.g. List) has data about the base sort, a creator function
;; (which takes the base sort and a list of sort parameters to apply and produces
;; an immutable datatype-instance. We also want to cache values for specific sort
;; parameters. 
(struct z3-complex-sort (base-sort creator instance-hash))

;; Lists are a builtin complex sort. z3:mk-list-sort already returns a
;; datatype-instance.
(define (make-list-sort base-sort params)
  (if (= (length params) 1)
      (z3:mk-list-sort (current-context) (make-symbol (gensym)) (first params))
      (raise (make-exn:fail "List sort should have just one parameter!"))))

(struct z3-context-info (context namespace sort-table))

;; Wraps a binary function so that arguments are processed
;; in a right-associative manner.
(define (rassoc fn)
  (lambda args
    (foldr fn (last args) (drop-right args 1))))

(define (flip fn) (lambda (x y) (fn y x)))

;; Wraps a binary function so that arguments are processed
;; in a left-associative manner. Note that foldl calls functions
;; in their reverse order, so we flip the arguments to fix that.
(define (lassoc fn)
  (lambda (fst . rst)
    (foldl (flip fn) fst rst)))

; XXX this is broken
(define (chainable fn)
  (lambda (fst . rst)
    (apply z3:mk-and (foldl (flip fn) fst rst))))

;; Curry a function application exactly *once*. The second time function
;; arguments are applied, the application is evaluated.
(define-syntax-rule (curry-once fn arg ...)
  (lambda more-args
    (displayln (format "Calling function: ~a with args ~a" 'fn more-args))
    (apply fn (append (list arg ...) more-args))))

(define-syntax-rule (builtin var fn ctx)
  (list 'var (fn ctx)))

(define-syntax builtin-curried
  (syntax-rules ()
    [(_ var fn ctx) (list 'var (curry-once fn ctx))]
    [(_ var fn ctx wrap) (list 'var (wrap (curry-once fn ctx)))]))

(define (new-context-info model?)
  (define ctx (z3:mk-context (make-config #:model? model?)))
  (define ns (make-empty-namespace))
  (define sorts (make-hash))
  ; Sorts go into a separate table
  (for-each (lambda (arg)
              (hash-set! sorts (first arg) (second arg)))
            (list
             (builtin Bool z3:mk-bool-sort ctx)
             (builtin Int z3:mk-int-sort ctx)
             (builtin-curried BitVec z3:mk-bv-sort ctx)
             ; The base sort for lists is irrelevant
             (list 'List (z3-complex-sort #f make-list-sort (make-hash)))))
  (for-each (lambda (arg)
              (namespace-set-variable-value! (first arg) (second arg) #t ns))
            (list
             (builtin true z3:mk-true ctx)
             (builtin false z3:mk-false ctx)
             (builtin-curried = z3:mk-eq ctx)
             (builtin-curried distinct z3:mk-distinct ctx)
             (builtin-curried not z3:mk-not ctx)
             (builtin-curried ite z3:mk-ite ctx)
             (builtin-curried iff z3:mk-iff ctx)
             (builtin-curried z3:mk-implies ctx rassoc)
             (builtin-curried xor z3:mk-xor ctx lassoc)
             ; These functions already accept an arbitrary number of arguments
             (builtin-curried and z3:mk-and ctx)
             (builtin-curried or z3:mk-or ctx)
             (builtin-curried + z3:mk-add ctx)
             (builtin-curried * z3:mk-mul ctx)
             (builtin-curried - z3:mk-sub ctx)
             ; These don't
             (builtin-curried / z3:mk-div ctx lassoc)
             (builtin-curried div z3:mk-div ctx lassoc)
             (builtin-curried mod z3:mk-mod ctx lassoc)
             (builtin-curried rem z3:mk-rem ctx lassoc)
             ; XXX Comparisons are chainable (i.e. (< a b c) == (and (< a b) (< b c)))
             (builtin-curried < z3:mk-lt ctx)
             (builtin-curried <= z3:mk-le ctx)
             (builtin-curried > z3:mk-gt ctx)
             (builtin-curried >= z3:mk-ge ctx)))
  (z3-context-info ctx ns sorts))

(define-syntax-rule (with-context info2 body ...)
  (let ([info info2])
    (parameterize ([ctx (z3-context-info-context info)]
                   [ctx-namespace (z3-context-info-namespace info)]
                   [ctx-sort-table (z3-context-info-sort-table info)])
    body ...)))

;; Handle the next error.
(define (handle-next-error)
  (define err (z3:get-error-code (ctx)))
  (raise-user-error "~s" (z3:get-error-msg err)))

;; Set the logic for this context. This can only be called once.
(define (set-logic logic)
  (let ([rv
         (z3:set-logic (ctx) (symbol->string logic))])
    (when (not rv) (handle-next-error))))

;; Helper function to make a symbol with the given name (Racket symbol)
(define (make-symbol symbol-name)
  (z3:mk-string-symbol (ctx) (symbol->string symbol-name)))
   
;; Declare a new sort. num-params is currently ignored.
(define-syntax-rule (declare-sort sort num-params)
  (set-value 'sort
             (z3:mk-uninterpreted-sort (ctx) (make-symbol 'sort))))

;; sort-exprs are sort ids, (_ id parameter*), or (id sort-expr*).
(define (sort-expr->z3-sort expr)
  (match expr
    [(list '_ id params ...) (apply (get-sort id) params)]
    [(list id args ...) (apply (get-sort id) (map get-sort args))]
    [id (get-sort id)]))

(define (trace expr)
  (displayln (format "TRACE: ~a" expr))
  expr)

;; Given an expr, convert it to a Z3 AST. This is a really simple recursive descent parser.
(define (expr->z3-ast expr)
  (displayln (format "IN: ~a" expr))
  (define ast (match expr
    ; Non-basic expressions
    [(list fn args ...) (apply (get-value fn) (map expr->z3-ast args))]
    ; Numerals
    [(? exact-integer?) (z3:mk-numeral (ctx) (number->string expr) (get-sort 'Int))]
    [(? inexact-real?) (z3:mk-numeral (ctx) (number->string expr) (get-sort 'Real))]
    ; Anything else should be in the namespace
    [id (get-value id)]))
  (displayln (format "Output: ~a ~a ~a" expr ast (z3:ast-to-string (current-context) ast)))
  ast)

;; Declare a new function. argsort is a sort-expr.
(define-syntax (declare-fun stx)
  (syntax-case stx ()
    [(declare-fun fn (argsort ...) retsort)
     #'(let ([args (vector (sort-expr->z3-sort 'argsort) ...)]
             [ret (sort-expr->z3-sort 'retsort)])
         (if (= 0 (vector-length args))
             (set-value 'fn (z3:mk-const (ctx) (make-symbol 'fn) ret))
             (set-value 'fn (z3:mk-func-decl (ctx) (make-symbol 'fn) args ret)))
         (void))]))

(define-syntax-rule (assert expr)
  (begin
    (displayln 'expr)
    (z3:assert-cnstr (ctx) (expr->z3-ast 'expr))))

(define (check-sat) (z3:check (ctx)))

(provide current-context
         with-context
         new-context-info
         declare-sort
         declare-fun
         assert
         check-sat
         (contract-out
          [set-logic (-> symbol? any)]))