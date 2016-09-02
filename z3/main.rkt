#lang typed/racket/base

(require "ffi.rkt" "smt.rkt")
(provide (all-from-out "ffi.rkt" "smt.rkt"))

;; Hack just because I don't know how to run tests on `raco pkg install`
(require (for-syntax racket/base))
(begin-for-syntax
  (require "tests/guide.rkt"))
