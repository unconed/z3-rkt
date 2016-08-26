[![Build Status](https://travis-ci.org/philnguyen/z3-rkt.svg?branch=master)](https://travis-ci.org/philnguyen/z3-rkt)

`z3-rkt`: Racket bindings for Z3
================================

This package provides an implementation of Z3 in Racket.
Although I develop this package specifically for use in my symbolic execution,
it should be usable for general-purpose Racket SMT integration.
I originally forked from [Siddharth Agarwal's repository](https://github.com/sid0/z3.rkt), then:
* gave Typed Racket bindings; ported all but the ffi layer to Typed Racket
* generalized `declare-datatypes` to allow complex and recursive datatypes
* migrated from the deprecated API (which was very unresponsive to timeouts and had strange memory behavior) to the new Solver API
* ditched all deprecated functions
* ditched all hacky sort-instance functions (will generalize it later)

Old exapmles that used sort instances are not working for now.

Installing
----------

`z3-rkt` has been tested with Z3 4.4.1, which you can download and build from [https://github.com/Z3Prover/z3](https://github.com/Z3Prover/z3).

After installing, set environment variable `Z3_LIB` to the directory containing the Z3 library.
The file is named `z3.dll`, `libz3.so` or `libz3.dylib`, depending on your system being Windows, Mac, or Linux, respectively.

Tutorial is in [`tutorial.md`](https://github.com/philnguyen/z3-rkt/blob/master/tutorial.md)

Structure
----------

* [`ffi/`](https://github.com/philnguyen/z3.rkt/tree/master/ffi) defines low-level Z3 API
* [`smt/`](https://github.com/philnguyen/z3.rkt/tree/master/smt) defines the high-level Z3 API, close to the SMT2 language.
  This is the reccommended way to interact with Z3.
  

License
-------

Licensed under the Simplified BSD License. See the LICENSE file for more
details.

Please note that this license does not apply to Z3, only to these bindings.
