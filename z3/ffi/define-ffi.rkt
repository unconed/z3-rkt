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
      ;; If the api is absent, the user will get back a function that fails when invoked.
      ;; The `min-api` and/or `max-api` tags here only for an informative error message
      ;; instructing the user to get the appropriate Z3 version.
      (~optional (~seq #:min-api min-api:z3-vsn) #:defaults ([min-api #'#f]))
      (~optional (~seq #:max-api max-api:z3-vsn) #:defaults ([max-api #'#f])))
   (define lo (syntax-e #'min-api))
   (define hi (syntax-e #'max-api))
   (cond
     [(or lo hi)
      (define/with-syntax get-version (format-id #'x "get-version"))
      (define/with-syntax msg
        (string-append (format "`~a` needs Z3 " (syntax-e #'x))
                       (cond [(and lo hi) (format "not befor ~a and not after ~a" lo hi)]
                             [lo          (format "not before ~a" lo)]
                             [else        (format "not after ~a" hi)])))
      #'(define x (get-ffi-obj c-name libz3 t
                               (λ ()
                                 ;; It's not yet safe to invoke `get-version` here
                                 ;; unless `get-version` is guaranteed to have been genereated.
                                 (log-warning "~a. Generating dummy binding." msg)
                                 (λ _
                                   (define-values (major minor build _) (get-version))
                                   (error 'x "~a. Detected version is ~a.~a.~a" msg major minor build)))))]
     [else
      #'(define x (get-ffi-obj c-name libz3 t))])])
