# Ergo

Git: http://github.com/accordproject/ergo-compiler

**_WARNING_ The content of this repository is work in progress and subject to change**

## Rebuild Ergo from the source

The core of the Ergo compiler is extracted from a formal specification
in Coq to JavaScript.

The code is located in the following directories:
- in `mechanization` the Coq code (includes the abstract syntax tree, intermediate languages, and compiler to JavaScript)
- in `extraction` support code in OCaml (includes the parser)
- in `lib` the JavaScript API and command-line interface

### Dependencies

To rebuild the compiler from the source, you will need Coq 8.7 (or
later) and OCaml 4.05 (or later) with some additional libraries.

We recommend to install those using opam (https://opam.ocaml.org), the
OCaml package manager. Once you have installed opam, you can add the
necessary libraries as follow:

```
$ opam repo add coq-released https://coq.inria.fr/opam/released
$ opam install ocamlbuild menhir camlp5 base64 js_of_ocaml js_of_ocaml-ppx atdgen coq.8.7.2
$ opam install coq-qcert.1.0.7
```

### Build the Ergo Compiler

To recompile Ergo from its source, do:

```
$ make cleanall
$ make ergo
```

## License

Ergo is distributed under the terms of the Apache 2.0 License, see
[LICENSE](LICENSE)

Copyright 2018 Clause, Inc.

