# Ergo Documentation

![Ergo](.gitbook/assets/ergologo.png)
![Build Status](https://travis-ci.org/accordproject/ergo.svg?branch=master)
![CircleCI](https://circleci.com/gh/accordproject/ergo.svg?style=shield)
![lerna](https://img.shields.io/badge/maintained%20with-lerna-cc00ff.svg)
[![Documentation Status](https://readthedocs.org/projects/ergo/badge/?version=latest)](http://ergo.readthedocs.io/en/latest/?badge=latest)

Git: [http://github.com/accordproject/ergo](http://github.com/accordproject/ergo) / Website: [http://accordproject.github.io/ergo](http://accordproject.github.io/ergo)

_**WARNING**_** The content of this repository is work in progress and subject to change**

## About

This is the source code for the Ergo compiler. Ergo is the DSL for Smart _Legal_ Contracts.

The current target for the compiler is JavaScript.

## Getting started

### Install

To install the Ergo compiler and command-line, do:

```text
$ npm install @accordproject/ergo-cli -g
```

To check that the compiler has been installed, and see which version number:

```text
$ ergoc --version
```

To get command line help:

```text
$ ergoc --help
$ ergoc compile --help
$ ergoc execute --help
```

### Compiling your first contract

Once installed, you can compile your first Ergo contract to JavaScript:

```text
$ ergoc compile --ergo ./examples/volumediscount/logic.ergo --cto ./examples/volumediscount/model.cto
```

### Execute a contract clause

To compile and _execute_ a given clause in a contract:

```text
$ ergoc execute --ergo ./examples/volumediscount/logic.ergo --contractname VolumeDiscount --clausename volumediscount --contract ./examples/volumediscount/contract.json --request ./examples/volumediscount/request.json --state ./examples/volumediscount/state.json --cto ./examples/volumediscount/model.cto
{"response":{"discountRate":2.8,"$class":"org.accordproject.volumediscount.VolumeDiscountResponse"},"state":{"$class":"org.accordproject.contract.State","status":"EXECUTORY"}}
```

## Documentation

Documentation is work in progress. The latest documentation release is available at [http://ergo.readthedocs.io](http://ergo.readthedocs.io)

## For developers

[Contributing Guidelines](contribute-to-ergo/contributing.md)

[Developer Guidance](contribute-to-ergo/developers/)

## License

Ergo is distributed under the terms of the Apache 2.0 License, see [LICENSE](https://github.com/accordproject/ergo/blob/master/LICENSE)

Copyright 2018 Clause, Inc.

