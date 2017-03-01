#lang racket/base

(provide define-z3)

(require ffi/unsafe
         syntax/parse/define)

(define libz3
  (let-values
      ([(lib-name default-dir)
        (case (system-type 'os)
          [(unix) (values "libz3.so" #f)]
          [(windows) (values "libz3.dll" #f)]
          [(macosx)
           (values "libz3.dylib"
                   ;; Homebrew puts it there
                   "/usr/local/lib/")])]
       [(Z3_LIB) "Z3_LIB"])
    (define libz3-path (or (getenv Z3_LIB) default-dir))
    (cond
      [libz3-path
       (define libz3-without-suffix
         (path-replace-extension (build-path libz3-path lib-name) ""))
       (ffi-lib libz3-without-suffix)]
      [else
       (error 'z3-rkt
              "Cannot locate Z3 libary. Please set ${~a} to the directory containing ~a"
              Z3_LIB
              lib-name)])))

(define-simple-macro (define-z3 x:id c-name:str t)
  (define x (get-ffi-obj c-name libz3 t)))
