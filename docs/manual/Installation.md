Installation
============

Install with npm
----------------

Before you can run Ergo, you must install and configure the following dependencies on your
machine:

* [Node.js v8.x (LTS)](http://nodejs.org): We use Node to generate the documentation, run a
  development web server, run tests, and generate distributable files. Depending on your system,
  you can install Node either from source or as a pre-packaged bundle.

  We recommend using [nvm](https://github.com/creationix/nvm) (or
  [nvm-windows](https://github.com/coreybutler/nvm-windows))
  to manage and install Node.js, which makes it easy to change the version of Node.js per project.

To install the Ergo compiler and command-line, do:
```
$ npm install @accordproject/ergo-cli -g
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

