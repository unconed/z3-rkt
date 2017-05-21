#lang racket/base

(provide define-z3)

(require ffi/unsafe
         syntax/parse/define
         (for-syntax racket/base
                     racket/syntax
                     syntax/parse))

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

(begin-for-syntax
  (define-syntax-class z3-vsn
    #:description "Z3 version string of form major.minor.revision"
    (pattern v:id #:when (regexp-match? #rx"^[0-9]+\\.[0-9]+\\.[0-9]$"
                                        (symbol->string (syntax-e #'v))))))


(define-syntax-parser define-z3
  [(_ x:id c-name:str t
      (~optional (~seq #:min-api api:z3-vsn) #:defaults ([api #'#f])))
   (cond
     [(syntax-e #'api)
      #'(define x (get-ffi-obj c-name libz3 t
                               (λ ()
                                 (log-warning "Cannot find symbol `~a` in Z3 library. Generating dummy binding.")
                                 (λ _ (error 'x "requires Z3 >= ~a" 'api)))))]
     [else
      #'(define x (get-ffi-obj c-name libz3 t))])])
