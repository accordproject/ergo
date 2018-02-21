# Jura

Git: http://github.com/accordproject/jura-compiler

**_WARNING_ The content of this repository is work in progress and subject to change**

## About

This is the source code for the Jura compiler. Jura is a DSL for Smart *Legal* Contracts.

The current target for that compiler is JavaScript.

## Getting started

### Install

To install the Jura compiler and command-line, do:
```
$ npm install jura-compiler -g
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
$ jurac compile --jura ./tests/volumediscount.jura
```

### Execute a contract clause

To compile and _execute_ a given clause in a contract:

```
$ jurac execute --jura ./tests/volumediscount.jura --contractname VolumeDiscount --clausename volumediscount --clause ./tests/volumediscount-clause.json --request ./tests/volumediscount-request.json 
{"discountRate":2.8,"$class":"org.accordproject.volumediscount.VolumeDiscountResponse"}
```

## Documentation

There is no official documentation yet, but you can find a few notes on the language in [./doc/Language.md](./doc/Language.md)

## For developers

### Install development version

To install the latest development code, clone this git repository and do a local install:
```
$ git clone https://github.com/accordproject/jura-compiler.git
$ cd ./jura-compiler
$ npm install -g
```

### Build from source

Instructions for how to rebuild the compiler from the source can be found in [BUILD.md](BUILD.md).

## License

Jura is distributed under the terms of the Apache 2.0 License, see
[LICENSE](LICENSE)

Copyright 2018 Clause, Inc.

