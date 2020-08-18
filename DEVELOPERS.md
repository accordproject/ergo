# Ergo Development Guide

## ❗ Accord Project Development Guide ❗
We'd love for you to help develop improvements to Ergo technology! Please refer to the [Accord Project Development guidelines][apdev] we'd like you to follow.

## Ergo Specific Information

### Overview

This document describes how to set up your development environment to build and test Ergo, and explains the basic mechanics of using `git`, `node`, `lerna`.

The core of the Ergo compiler is extracted from a formal specification in Coq to JavaScript.

The code is located in the following directories:

* in `mechanization` the Coq code (includes the abstract syntax tree, intermediate languages, and compiler to JavaScript)
* in `extraction` support code in OCaml (includes the parser)
* in `packages` the JavaScript packages, containing the Ergo compiler API and command-line tools

### Development Setup

#### Installing Prerequisites

Before you can build Ergo, you must install and configure the following prerequisites on your machine:

* [Lerna](https://lerna.js.org): We use lerna to handle multiple npm packages in the Ergo repository. To install:

```sh
$ npm install -g lerna@^3.15.0
```

* [opam](https://opam.ocaml.org): the OCaml package manager, for OCaml 4.11.2. To install:

```sh
$ sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
$ eval $(opam env)
$ opam switch create 4.11.2
```

#### Install development version

To install the latest development code, clone this git repository and do a local install:

```sh
$ git clone https://github.com/accordproject/ergo.git
$ cd ./ergo/packages/ergo-cli
$ npm install -g
```

##### Dependencies

To rebuild the compiler from the source, you will need Coq 8.12 and OCaml >=4.09.1, with some additional libraries. You can add the necessary libraries with opam as follow:
 
```sh
$ opam repo add coq-released https://coq.inria.fr/opam/released
$ opam install dune menhir base64 js_of_ocaml js_of_ocaml-ppx yojson atdgen re calendar uri wasm.1.0.1
$ opam install coq.8.12.2 coq-qcert.2.1.0
```

##### Build the Ergo Compiler and REPL

To recompile Ergo from its source, do:

```sh
$ make cleanall
$ make configure
$ make all
```

If successful, you should find the following binaries in the `bin/` directory:

* `ergoc.native`, the Ergo compiler
* `ergotop.native`, an experimental REPL for Ergo (note: the wrapper script
 `bin/ergotop` launches `ergotop.native` via the
 [`rlwrap`](https://github.com/hanslub42/rlwrap) utility, which must be
 installed separately)

####  Running the Unit Test Suite

We write unit and integration tests with Mocha and Cucumber. To run all of the tests once run:

```text
npm run test
```

###  Writing Documentation

The Ergo project uses [Docusaurus][docusaurus] for the language documentation.

Code documentation uses the following tools:
- [coq2html][coq2html] for the compiler specification (install with `opam install coq-coq2html`)
- [odoc][odoc] (install with `opam install odoc`)
- [JSDoc][jsdoc] for the JavaScript part of the code

This means that all the docs are stored inline in the source code and so are kept in sync as it changes.

This means that since we generate the documentation from the source code, we can easily provide version-specific documentation by simply checking out a version of Ergo and running the build.

---

Copyright 2018-2019 Clause, Inc.

[apdev]: https://github.com/accordproject/techdocs/blob/master/DEVELOPERS.md
[docusaurus]: http://docusaurus.io/
[coq2html]: https://github.com/xavierleroy/coq2html
[odoc]: https://github.com/ocaml/odoc
[jsdoc]: http://usejsdoc.org/

