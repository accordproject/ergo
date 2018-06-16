![Ergo](./website/static/img/ergo.png)

![Build Status](https://travis-ci.org/accordproject/ergo.svg?branch=master)
![CircleCI](https://circleci.com/gh/accordproject/ergo.svg?style=shield)
![lerna](https://img.shields.io/badge/maintained%20with-lerna-cc00ff.svg)
[![npm version](https://badge.fury.io/js/%40accordproject%2Fergo-cli.svg)](https://badge.fury.io/js/%40accordproject%2Fergo-cli)

[http://ergo.accordproject.org](http://ergo.accordproject.org)

## About

This is the source code for the Ergo compiler. Ergo is the [Accord Project](https://accordproject.org/) language for Smart Legal Contracts.

The Ergo compiler is distributed as an [npm package](https://www.npmjs.com/package/@accordproject/ergo-cli). If you want to try Ergo, consult the [Getting started](./#getting-started) section.

The Ergo compiler is written in [Coq](https://coq.inria.fr) with a parser and some support code written in [OCaml](https://ocaml.org). It makes extensive use of the [Q*cert compiler](https://querycert.github.io) for code generation.

Both the Ergo language and its compiler are in early development phase. If you would like to contribute, consult the [For Developers](./#for-developers) section.

## Documentation

The most recent documentation for Ergo is available at [https://ergo.accordproject.org/](https://ergo.accordproject.org/)

## Getting started

### Try it out

If you simply want to get a peek at Ergo without installing anything, check out the examples on the [Ergo Playground](https://accordproject.github.io/ergo-playground/).

### Install Ergo

The easiest way to install Ergo is as a [Node.js package](https://nodejs.org/). Once you have Node.js installed on your machine, you can get the Ergo compiler and command-line using the Node.js package manager by typing the following in a terminal:

```text
$ npm install -g @accordproject/ergo-cli
```

This will install the compiler itself (`ergoc`) and a command-line tool (`ergo`) to execute Ergo code. You can check that both have been installed and print the version number by typing the following in a terminal:

```text
$ ergoc --version
$ ergo --version
```

Then, to get command line help:

```text
$ ergoc --help
$ ergo execute --help
```

### Compiling your first contract

To compile your first Ergo contract to JavaScript:

```text
$ ergoc ./examples/volumediscount/model.cto ./examples/volumediscount/logic.ergo
15:17:08 - info: Logging initialized. 2018-05-24T19:17:08.024Z
Processing file: ./examples/volumediscount/logic.ergo -- compiled to: ./examples/volumediscount/logic.js
```

### Execute a contract

To compile and execute that contract:

```text
$ ergo execute --cto ./examples/volumediscount/model.cto --ergo ./examples/volumediscount/logic.ergo --contractname VolumeDiscount --contract ./examples/volumediscount/contract.json --request ./examples/volumediscount/request.json --state ./examples/volumediscount/state.json
15:18:41 - info: Logging initialized. 2018-05-24T19:18:41.009Z
15:18:41 - info: {"emit":[],"state":{"$class":"org.accordproject.contract.State","status":"EXECUTORY"},"response":{"discountRate":2.8,"$class":"org.accordproject.volumediscount.VolumeDiscountResponse"}}
```

## For developers

We welcome contributions. We encourage contributors to consult the following [Guidelines](./CONTRIBUTING.md)

To setup for development, please consult the [Developer Guide](./DEVELOPERS.md)

## License <a name="license"></a>
Accord Project source code files are made available under the Apache License, Version 2.0 (Apache-2.0), located in the LICENSE file. Accord Project documentation files are made available under the Creative Commons Attribution 4.0 International License (CC-BY-4.0), available at http://creativecommons.org/licenses/by/4.0/.

Copyright 2018 Clause, Inc.

