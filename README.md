[![Build Status](https://travis-ci.org/philnguyen/z3-rkt.svg?branch=master)](https://travis-ci.org/philnguyen/z3-rkt)

Racket bindings for Z3
================================

This package provides an implementation of Z3 in Racket.
Although I develop this package specifically for use in my symbolic execution,
it should be usable for general-purpose Racket SMT integration.
I originally forked it from [Siddharth Agarwal's repository](https://github.com/sid0/z3.rkt), then:
* ported everything to Typed Racket:
* generalized `declare-datatypes` to allow complex and recursive datatypes
* migrated from the deprecated API to the new Solver API
* ditched all deprecated functions
* added macro-expansion time scraping of the documentation to automatically generate all FFI bindings (ish) and Typed Racket bindings

Old examples that used sort instances are not working for now.

Installing
----------

### Install Z3

- `z3-rkt` has been tested with Z3 4.4.1, which you can download and build from [https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3). The Travis CI script clones current Z3 from Github.

### Install Z3 Racket bindings

- After installing Z3, set environment variable `Z3_LIB` to the directory containing the Z3 library.
The library file is named `z3.dll`, `libz3.so` or `libz3.dylib`, depending on your system being Windows, Mac, or Linux, respectively.

- TODO: decide package name (`-rkt` is redundant) and register.

- Some examples mimicking the [Z3 guide](http://rise4fun.com/Z3/tutorial/guide) are in [`tests/guide.rkt`](https://github.com/philnguyen/z3-rkt/blob/master/tests/guide.rkt).

Structure
----------

* [`ffi/`](https://github.com/philnguyen/z3.rkt/tree/master/ffi) defines bindings for low-level Z3 API. The interface is automatically generated at compile-time from the [documentation](http://research.microsoft.com/en-us/um/redmond/projects/z3/code/group__capi.html). A snapshot of the bindings in Typed Racket is in [snapshot/main.rkt](https://github.com/philnguyen/z3-rkt/blob/master/ffi/snapshot/main.rkt). The low-level Racket interface differs from C in a predictable way, apart from naming conventions:
  
  | C                                          | Racket
  |--------------------------------------------|----------------------------------------
  | multiple out parameters                    | multiple return values
  | input array(s) with user supplied length(s)| list or list of tuples with computed length
  | result with success flag                   | optional result, which is either a union or a sum, depending on whether the result overlaps with `Boolean`


* [`smt/`](https://github.com/philnguyen/z3.rkt/tree/master/smt) defines the high-level Z3 API, close to the SMT2 language.
  This is the reccommended way to interact with Z3.
  Examples in [`tests/guide.rkt`](https://github.com/philnguyen/z3-rkt/blob/master/tests/guide.rkt) use this
  
TODO
----------

- [ ] Mutually recursive datatypes
- [ ] Parameterized sorts. This feature does not exist at the C API level.
- [ ] Several missing functions without `def_API` lines from doc
- [ ] Scribble?
- [ ] Figure out package name
- [ ] Figure out how to make package and register

License
-------

Licensed under the Simplified BSD License. See the LICENSE file for more
details.

Please note that this license does not apply to Z3, only to these bindings.
