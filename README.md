![Jura](./docs/juralogo.png)

#

[![Build Status](https://travis-ci.org/accordproject/jura.svg?branch=master)](https://travis-ci.org/accordproject/jura)
[![CircleCI](https://circleci.com/gh/accordproject/jura.svg?style=shield)](https://circleci.com/gh/accordproject/jura)
[![lerna](https://img.shields.io/badge/maintained%20with-lerna-cc00ff.svg)](https://lernajs.io/)

Git: http://github.com/accordproject/jura / Pages: https://accordproject.github.io/jura

**_WARNING_ The content of this repository is work in progress and subject to change**

## About

This is the source code for the Jura compiler. Jura is the DSL for Smart *Legal* Contracts.

The current target for the compiler is JavaScript.

## Getting started

### Install

To install the Jura compiler and command-line, do:
```
$ npm install jura-cli -g
```

To check that the compiler has been installed, and see which version number:
```
$ jurac --version
```

To get command line help:
```
$ jurac --help
$ jurac compile --help
$ jurac execute --help
```

### Compiling your first contract

Once installed, you can compile your first Jura contract to JavaScript:
```
$ jurac compile --jura ./examples/volumediscount/logic.jura --cto ./examples/volumediscount/model.cto
```

### Execute a contract clause

To compile and _execute_ a given clause in a contract:

```
$ jurac execute --jura ./examples/volumediscount/logic.jura --contractname VolumeDiscount --clausename volumediscount --contract ./examples/volumediscount/contract.json --request ./examples/volumediscount/request.json --cto ./examples/volumediscount/model.cto
{"discountRate":2.8,"$class":"org.accordproject.volumediscount.VolumeDiscountResponse"}
```

## Documentation

There is no official documentation yet, but you can find a few notes on the language in [./docs/Language.md](./docs/Language.md)

## For developers

### Install development version

To install the latest development code, clone this git repository and do a local install:
```
$ git clone https://github.com/accordproject/jura.git
$ cd ./jura/packages/jura-cli
$ npm install -g
```

### Build from source

Instructions for how to rebuild the compiler from the source can be found in [BUILD.md](BUILD.md).

## License

Jura is distributed under the terms of the Apache 2.0 License, see
[LICENSE](LICENSE)

Copyright 2018 Clause, Inc.

