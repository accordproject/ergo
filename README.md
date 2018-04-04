![Ergo](./docs/ergologo.png)

#

[![Build Status](https://travis-ci.org/accordproject/ergo.svg?branch=master)](https://travis-ci.org/accordproject/ergo)
[![CircleCI](https://circleci.com/gh/accordproject/ergo.svg?style=shield)](https://circleci.com/gh/accordproject/ergo)
[![lerna](https://img.shields.io/badge/maintained%20with-lerna-cc00ff.svg)](https://lernajs.io/)

Git: http://github.com/accordproject/ergo / Pages: https://accordproject.github.io/ergo

**_WARNING_ The content of this repository is work in progress and subject to change**

## About

This is the source code for the Ergo compiler. Ergo is the DSL for Smart *Legal* Contracts.

The current target for the compiler is JavaScript.

## Getting started

### Install

To install the Ergo compiler and command-line, do:
```
$ npm install ergo-cli -g
```

To check that the compiler has been installed, and see which version number:
```
$ ergoc --version
```

To get command line help:
```
$ ergoc --help
$ ergoc compile --help
$ ergoc execute --help
```

### Compiling your first contract

Once installed, you can compile your first Ergo contract to JavaScript:
```
$ ergoc compile --ergo ./examples/volumediscount/logic.ergo --cto ./examples/volumediscount/model.cto
```

### Execute a contract clause

To compile and _execute_ a given clause in a contract:

```
$ ergoc execute --ergo ./examples/volumediscount/logic.ergo --contractname VolumeDiscount --clausename volumediscount --contract ./examples/volumediscount/contract.json --request ./examples/volumediscount/request.json --state ./examples/volumediscount/state.json --cto ./examples/volumediscount/model.cto
{"discountRate":2.8,"$class":"org.accordproject.volumediscount.VolumeDiscountResponse"}
```

## Documentation

There is no official documentation yet, but you can find a few notes on the language in [./docs/Language.md](./docs/Language.md)

## For developers

### Install development version

To install the latest development code, clone this git repository and do a local install:
```
$ git clone https://github.com/accordproject/ergo.git
$ cd ./ergo/packages/ergo-cli
$ npm install -g
```

### Build from source

Instructions for how to rebuild the compiler from the source can be found in [BUILD.md](BUILD.md).

## License

Ergo is distributed under the terms of the Apache 2.0 License, see
[LICENSE](LICENSE)

Copyright 2018 Clause, Inc.

