# Ergo

![Build Status](https://travis-ci.org/accordproject/ergo.svg?branch=master)
![CircleCI](https://circleci.com/gh/accordproject/ergo.svg?style=shield)
![lerna](https://img.shields.io/badge/maintained%20with-lerna-cc00ff.svg)
[![Documentation Status](https://readthedocs.org/projects/ergo/badge/?version=latest)](http://ergo.readthedocs.io/en/latest/?badge=latest)
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

To check that the compiler has been installed, and see which version number:

```text
$ ergo --version
```

To get command line help:

```text
$ ergo --help
$ ergo compile --help
$ ergo execute --help
```

### Compiling your first contract

Once installed, you can compile your first Ergo contract to JavaScript:

```text
$ ergoc --ergo ./examples/volumediscount/logic.ergo --cto ./examples/volumediscount/model.cto
```

### Execute a contract clause

To compile and _execute_ a given clause in a contract:

```text
$ ergo execute --ergo ./examples/volumediscount/logic.ergo --contractname VolumeDiscount --clausename volumediscount --contract ./examples/volumediscount/contract.json --request ./examples/volumediscount/request.json --state ./examples/volumediscount/state.json --cto ./examples/volumediscount/model.cto
{"response":{"discountRate":2.8,"$class":"org.accordproject.volumediscount.VolumeDiscountResponse"},"state":{"$class":"org.accordproject.contract.State","status":"EXECUTORY"}}
```

## Documentation

Documentation is work in progress. The latest documentation release is available at [http://ergo.readthedocs.io](http://ergo.readthedocs.io)

## For developers

[Contributing Guidelines](contribute-to-ergo/contributing.md)

[Developer Guidance](contribute-to-ergo/developers/)

## License <a name="license"></a>
Accord Project source code files are made available under the Apache License, Version 2.0 (Apache-2.0), located in the LICENSE file. Accord Project documentation files are made available under the Creative Commons Attribution 4.0 International License (CC-BY-4.0), available at http://creativecommons.org/licenses/by/4.0/.

Copyright 2018 Clause, Inc.

