![Ergo](./ergo.png)

![Build Status](https://travis-ci.org/accordproject/ergo.svg?branch=master)
![CircleCI](https://circleci.com/gh/accordproject/ergo.svg?style=shield)
![lerna](https://img.shields.io/badge/maintained%20with-lerna-cc00ff.svg)
[![npm version](https://badge.fury.io/js/%40accordproject%2Fergo-cli.svg)](https://badge.fury.io/js/%40accordproject%2Fergo-cli)

[https://docs.accordproject.org/docs/ergo](https://docs.accordproject.org/docs/ergo.html)

## About

This is the source code for the Ergo compiler. Ergo is the [Accord
Project](https://accordproject.org/) language for Smart Legal Contracts.

The Ergo compiler is distributed as an [npm
package](https://www.npmjs.com/package/@accordproject/ergo-cli). If
you want to install Ergo, consult the [getting
started](#getting-started) section.

The Ergo compiler is written in [Coq](https://coq.inria.fr) with a parser and
some support code written in [OCaml](https://ocaml.org). It makes extensive use
of the [Q*cert compiler](https://querycert.github.io) for code generation.

Both the Ergo language and its compiler are in early development
phase. If you would like to build from source or to contribute,
consult the [for developers](#for-developers) section.

## Try it out

If you want to take a peek at Ergo without installing anything, check
out the interactive [REPL](https://ergorepl.netlify.com)
(read-eval-print-loop) for Ergo stand-alone, or the [Accord Project
Template Studio](https://studio.accordproject.org) showing how Ergo
can express the logic of legal templates.

## Documentation

The most recent documentation for the Ergo language and compiler is
available at
[https://docs.accordproject.org/docs/ergo.html](https://docs.accordproject.org/docs/ergo)

## Getting started

### Install Ergo

The easiest way to install Ergo is as a [Node.js](https://nodejs.org/) package.
Once you have Node.js installed on your machine, you can get the Ergo compiler
and command-line using the Node.js package manager by typing the following in a
terminal:

```text
$ npm install -g @accordproject/ergo-cli
```

This will install the compiler itself (`ergoc`) and command-line tools (`ergorun` and `ergotop`) to create and invoke Ergo contracts. You can check that both have been installed and print the version number by typing the following in a terminal:

```text
$ ergoc --version
$ ergorun --version
```

Then, to get command line help:

```text
$ ergoc --help
$ ergorun --help
```

### Compiling your first contract

To compile your first Ergo contract to JavaScript:

```text
$ ergoc ./examples/volumediscount/model.cto ./examples/volumediscount/logic.ergo
15:17:08 - info: Logging initialized. 2018-05-24T19:17:08.024Z
Processing file: ./examples/volumediscount/logic.ergo -- compiled to: ./examples/volumediscount/logic.js
```

By default, Ergo compiles to JavaScript for execution. You can inspect
the compiled JavaScript code in `./examples/volumediscount/logic.js`

### Invoke a contract

To compile and invoke that contract:

```text
$ ergorun ./examples/volumediscount/model.cto ./examples/volumediscount/logic.ergo --contractname org.accordproject.volumediscount.VolumeDiscount --contract ./examples/volumediscount/contract.json --request ./examples/volumediscount/request.json --state ./examples/volumediscount/state.json
13:40:03 - info: Logging initialized. 2018-06-17T17:40:03.587Z
13:40:03 - info: {"response":{"discountRate":2.8,"$class":"org.accordproject.volumediscount.VolumeDiscountResponse"},"state":{"$class":"org.accordproject.cicero.contract.AccordContractState","stateId":"1"},"emit":[]}
```

## For developers

We welcome contributions. We encourage contributors to consult the following
[Guidelines](./CONTRIBUTING.md)

To setup for development, please consult the [Developer Guide](./DEVELOPERS.md)

## License <a name="license"></a>

Accord Project source code files are made available under the Apache License,
Version 2.0 (Apache-2.0), located in the [LICENSE](./LICENSE) file. Accord
Project documentation files are made available under the Creative Commons
Attribution 4.0 International License (CC-BY-4.0), available at
http://creativecommons.org/licenses/by/4.0/.

Copyright 2018-2019 Clause, Inc.

