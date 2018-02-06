# Jura

Git: http://github.com/accordproject/jura-compiler

**_WARNING_ The content of this repository is work in progress and subject to change**

## About

This is the source code for the Jura compiler. Jura is a DSL for Smart *Legal* Contracts.

The current target for that compiler is JavaScript.

## Install for Node.js

To install the compiler and command-line interface for Node.js, do:

```
npm install -g
```

## Use

### Compiling Jura to JavaScript

Once installed, you can compile your first Jura contract to JavaScript:

```
$ jurac compile --jura ./tests/volumediscount.jura
```

## Execute a contract clause

To compile and _execute_ a given clause in a contract:

```
$ jurac execute --jura ./tests/volumediscount.jura --contractname VolumeDiscount --clausename volumediscount --clause ./tests/volumediscount-clause.json --request ./tests/volumediscount-request.json 
{"discountRate":2.8,"$class":"org.accordproject.volumediscount.VolumeDiscountResponse"}
```

## For developers

Instructions for how to rebuild the compiler from the source can be found in [BUILD.md](BUILD.md).

## License

Jura is distributed under the terms of the Apache 2.0 License, see
[LICENSE](LICENSE)

Copyright 2018 Clause, Inc.

