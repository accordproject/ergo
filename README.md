![Ergo](./website/static/img/ergo.png)

![Build Status](https://travis-ci.org/accordproject/ergo.svg?branch=master)
![CircleCI](https://circleci.com/gh/accordproject/ergo.svg?style=shield)
![lerna](https://img.shields.io/badge/maintained%20with-lerna-cc00ff.svg)
[![npm version](https://badge.fury.io/js/%40accordproject%2Fergo-cli.svg)](https://badge.fury.io/js/%40accordproject%2Fergo-cli)

Git: [http://github.com/accordproject/ergo](http://github.com/accordproject/ergo) / Website: [http://ergo.accordproject.org](http://ergo.accordproject.org)

_**WARNING**_** The content of this repository is work in progress and subject to change**

## About

This is the source code for the Ergo compiler. Ergo is the Accord Project language for Smart _Legal_ Contracts.

## Getting started

### Install

To install the Ergo compiler and command-line, do:

```text
$ npm install @accordproject/ergo-cli -g
```

To check that the compiler and command-line tools have been installed and print the version number:

```text
$ ergoc --version
$ ergo --version
```

To get command line help:

```text
$ ergoc --help
$ ergo execute --help
```

### Compiling your first contract

Once installed, you can compile your first Ergo contract to JavaScript:

```text
$ ergoc ./examples/volumediscount/model.cto ./examples/volumediscount/logic.ergo
15:17:08 - info: Logging initialized. 2018-05-24T19:17:08.024Z
Processing file: ./examples/volumediscount/logic.ergo -- compiled to: ./examples/volumediscount/logic.js
```

### Execute a contract clause

To compile and _execute_ a given clause in a contract:

```text
$ ergo execute --ergo ./examples/volumediscount/logic.ergo --contractname VolumeDiscount --contract ./examples/volumediscount/contract.json --request ./examples/volumediscount/request.json --state ./examples/volumediscount/state.json --cto ./examples/volumediscount/model.cto
15:18:41 - info: Logging initialized. 2018-05-24T19:18:41.009Z
15:18:41 - info: {"emit":[],"state":{"$class":"org.accordproject.contract.State","status":"EXECUTORY"},"response":{"discountRate":2.8,"$class":"org.accordproject.volumediscount.VolumeDiscountResponse"}}
```

## Documentation

The most recent documentation is available at [https://ergo.accordproject.org/](https://ergo.accordproject.org/)

## For developers

[Contributing Guidelines](contribute-to-ergo/contributing.md)

[Developer Guidance](contribute-to-ergo/developers/)

## License <a name="license"></a>
Accord Project source code files are made available under the Apache License, Version 2.0 (Apache-2.0), located in the LICENSE file. Accord Project documentation files are made available under the Creative Commons Attribution 4.0 International License (CC-BY-4.0), available at http://creativecommons.org/licenses/by/4.0/.

Copyright 2018 Clause, Inc.

