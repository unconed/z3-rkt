[![Build Status](https://travis-ci.org/philnguyen/z3-rkt.svg?branch=master)](https://travis-ci.org/philnguyen/z3-rkt) Z3 library for Racket
================================

This package provides an implementation of Z3 in Racket.
Although I develop it specifically for use in my symbolic execution,
it should be usable for general-purpose Racket SMT integration.
I originally forked from Siddharth Agarwal's repository ([sid0/z3.rkt](https://github.com/sid0/z3.rkt)), then:
* ported the package to Typed Racket
* migrated from the deprecated API to the new Solver API
* ditched all deprecated functions
* generalized SMT constructs like `declare-datatypes`, `forall/s`, `exists/s`
* ~~added macro-expansion time scraping of the documentation to automatically generate all FFI bindings (ish) and Typed Racket bindings~~


Installation
----------

### Install Z3

- This package has been tested with Z3 4.4.1 on Linux. You can also download and build the lastest version from [https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3), which the Travis CI script uses.

### Install Z3 Racket library

- Set environment variable `Z3_LIB` to the *directory* containing the Z3 library.
The library file is named `libz3.dll`, `libz3.so` or `libz3.dylib`, depending on your system being Windows, Linux, or Mac, respectively.

- ~~By default, at installation, the package parses the [latest documentation](http://research.microsoft.com/en-us/um/redmond/projects/z3/code/group__capi.html) over the internet and generates Z3 bindings from there. To customize the documentation to build from, you can:~~
  + ~~Set environment variable `Z3_DOC_LOCAL` to a local file with the same format as the official documentation. If this is set, it takes priority over the next setting~~
  + ~~Set environment variable `Z3_DOC_HTTP` to an alternate HTTP link to the documentation~~

- Install Z3 bindings:
> raco pkg install z3

- Some examples mimicking the [Z3 guide](http://rise4fun.com/Z3/tutorial/guide)
  are in [`tests/guide.rkt`](https://github.com/philnguyen/z3-rkt/blob/master/z3/tests/guide.rkt).
  To run the tests:
> raco test tests/guide.rkt

The API
----------

* [`z3/ffi`](https://github.com/philnguyen/z3-rkt/blob/master/z3/ffi/ffi-typed.rkt)
  defines bindings for low-level Z3 API.
  The interface was originally generated from the
  [documentation](https://z3prover.github.io/api/html/group__capi.html).
  The [low-level Racket interface](https://github.com/philnguyen/z3-rkt/blob/master/z3/ffi/ffi.rkt) differs from C in a predictable way:
  
  | C                                                                       | Racket
  |-------------------------------------------------------------------------|----------------------------------------
  | `Z3_app_to_ast`, `Z3_is_app`, `Z3_stats_is_uint`, `Z3_solver_push`, etc.| `app->ast`, `app?`, `stats-is-uint?`, `solver-push!`, etc. (renaming based on both name and type)
  | multiple out parameters                                                 | multiple return values
  | input array(s) with user supplied length(s)                             | list or list of tuples with computed length(s). Tuples of size 2 are `Pairof _ _`s. Tuples of size 3+ are `List _ ...`s
  | out parameter `A` with result `Boolean` indicating success              | result `U Boolean A` or `U Boolean (List A)`, depending on whether `A` overlaps with `Boolean`

* [`z3/smt`](https://github.com/philnguyen/z3.rkt/tree/master/z3/smt) defines the high-level Z3 API, close to the SMT2 language.
  This is the reccommended way to interact with Z3.
  Examples in [`tests/guide.rkt`](https://github.com/philnguyen/z3-rkt/blob/master/z3/tests/guide.rkt) use this
  
TODO
----------

- [ ] `smt`: Mutually recursive datatypes
- [ ] `smt`: Parameterized sorts. This feature does not exist at the C API level.
- [ ] `ffi`: Several missing functions without `def_API` lines from doc
- [ ] Scribble?
- [x] Figure out package name
- [x] Figure out how to make package and register
- [ ] generate the typed wrapper automatically instead of having 2 version in sync currently

Known issues
-------------

- A minority of functions allow `null` arguments as valid use cases,
  which is mentioned in prose in the doc.
  I'm just hacking special cases that I need instead of flooding the API with `null`s.
- The bindings were originally generated automatically,
  and all names with `-to-` were converted to `->`.
  While most of them are appropriate, some of them aren't.

License
-------

Licensed under the Simplified BSD License. See the LICENSE file for more
details.

Please note that this license does not apply to Z3, only to these bindings.
