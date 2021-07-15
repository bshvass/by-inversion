Formalization of a prime field inversion algorithm by Bernstein and Yang
------------------------------------------------------------------------

This repository contains a formalization of the constant time prime field inversion algorithm from https://gcd.cr.yp.to/papers.html#safegcd in the Coq Proof Assistant. The files in `src` corresponds roughly to the sections in the paper describing the algorithm (e.g. `AppendixF.v` formalizes the theorems from Appendix F in https://gcd.cr.yp.to/papers.html#safegcd).

The folder `src/Comp1` contains an implementation of the computer proof of theorem F.22 in the paper. Use `make test-ocaml1` to run it; it should take about 8 hours to terminate.

The folder `src/Comp2` contains different implementations of the computational proof of theorem G.4 in the paper. The OCaml implementation is extracted directly from Coq. The binaries for these can be made with `make c` and `make ocaml`. The binaries take an integer as input and outputs the corresponding table entry from figure G.5 in https://gcd.cr.yp.to/papers.html#safegcd.

To compile all proofs you need to have Coq installed (version 8.12 or higher) and run `make` from the root folder.

On linux you also need to install csdp
  `sudo apt-get install coinor-csdp`
