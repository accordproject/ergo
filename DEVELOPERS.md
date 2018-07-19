# Developing Ergo

* [Overview](#overview)
* [Development Setup](#development-setup)
* [Coding Rules](#rules)
* [Commit Message Guidelines](.#commits)
* [Writing Documentation](.#documentation)

## Overview

This document describes how to set up your development environment to build and test Ergo, and explains the basic mechanics of using `git`, `node`, `lerna`.

The core of the Ergo compiler is extracted from a formal specification in Coq to JavaScript.

The code is located in the following directories:

* in `mechanization` the Coq code \(includes the abstract syntax tree, intermediate languages, and compiler to JavaScript\)
* in `extraction` support code in OCaml \(includes the parser\)
* in `packages` the JavaScript packages, containing the Ergo compiler API and command-line tools

##  Development Setup

### Installing Dependencies

Before you can build Ergo, you must install and configure the following dependencies on your machine:

* [Git](http://git-scm.com/): The \[Github Guide to Installing Git\]\[git-setup\] is a good source of information.
* [Node.js v8.x \(LTS\)](http://nodejs.org): We use Node to generate the documentation, run a development web server, run tests, and generate distributable files. Depending on your system, you can install Node either from source or as a pre-packaged bundle.

We recommend using [nvm](https://github.com/creationix/nvm) \(or [nvm-windows](https://github.com/coreybutler/nvm-windows)\) to manage and install Node.js, which makes it easy to change the version of Node.js per project.

* [Lerna](https://lernajs.io): We use lerna to handle multiple npm packages in the Ergo repository. To install:

```
npm install -g lerna
```

### Forking Ergo on Github

To contribute code to Ergo, you must have a GitHub account so you can push code to your own fork of Ergo and open Pull Requests in the \[GitHub Repository\]\[github\].

To create a Github account, follow the instructions [here](https://github.com/signup/free). Afterwards, go ahead and [fork](http://help.github.com/forking) the \[main Ergo repository\]\[github\].

### Install development version

To install the latest development code, clone this git repository and do a local install:

```text
$ git clone https://github.com/accordproject/ergo.git
$ cd ./ergo/packages/ergo-cli
$ npm install -g
```

#### Dependencies

To rebuild the compiler from the source, you will need Coq 8.8.1 and OCaml 4.07 with some additional libraries.

We recommend to install those using opam \([https://opam.ocaml.org](https://opam.ocaml.org)\), the OCaml package manager. Once you have installed opam, you can add the necessary libraries as follow:

```text
$ opam repo add coq-released https://coq.inria.fr/opam/released
$ opam install ocamlbuild menhir camlp5 base64 js_of_ocaml js_of_ocaml-ppx atdgen
$ opam install coq.8.8.1 coq-qcert.1.1.0
```

#### Build the Ergo Compiler and REPL

To recompile Ergo from its source, do:

```text
$ make cleanall
$ make
```

If successful, you should find the following binaries in the `bin/` directory:

* `ergoc.native`, the Ergo compiler
* `ergotop.native`, an experimental REPL for Ergo (note: the wrapper script
  `bin/ergotop` launches `ergotop.native` via the
  [`rlwrap`](https://github.com/hanslub42/rlwrap) utility, which must be
  installed separately)

###  Running the Unit Test Suite

We write unit and integration tests with Mocha. To run all of the tests once run:

```text
lerna run test
```

##  Coding Rules

To ensure consistency throughout the source code, keep these rules in mind as you are working:

* All features or bug fixes **must be tested** by one or more \[specs\]\[unit-testing\].
* All public API methods **must be documented** with jsdoc. To see how we document our APIs, please check out the existing source code and see the section about [writing documentation](./#documentation)
* With the exceptions listed below, we follow the rules contained in

  \[Google's JavaScript Style Guide\]\[js-style-guide\].

##  Git Commit Guidelines

We have very precise rules over how our git commit messages can be formatted. This leads to **more readable messages** that are easy to follow when looking through the **project history**. But also, we use the git commit messages to **generate the Ergo change log**.

The commit message formatting can be added using a typical git workflow or through the use of a CLI wizard \([Commitizen](https://github.com/commitizen/cz-cli)\). To use the wizard, run `yarn run commit` in your terminal after staging your changes in git.

### Commit Message Format

Each commit message consists of a **header**, a **body** and a **footer**. The header has a special format that includes a **type**, a **scope** and a **subject**:

```text
<type>(<scope>): <subject>
<BLANK LINE>
<body>
<BLANK LINE>
<footer>
```

The **header** is mandatory and the **scope** of the header is optional.

Any line of the commit message cannot be longer 100 characters! This allows the message to be easier to read on GitHub as well as in various git tools.

### Revert

If the commit reverts a previous commit, it should begin with `revert:`, followed by the header of the reverted commit. In the body it should say: `This reverts commit <hash>.`, where the hash is the SHA of the commit being reverted. A commit with this format is automatically created by the \[`git revert`\]\[git-revert\] command.

### Type

Must be one of the following:

* **feat**: A new feature
* **fix**: A bug fix
* **docs**: Documentation only changes
* **style**: Changes that do not affect the meaning of the code \(white-space, formatting, missing semi-colons, etc\)
* **refactor**: A code change that neither fixes a bug nor adds a feature
* **perf**: A code change that improves performance
* **test**: Adding missing or correcting existing tests
* **chore**: Changes to the build process or auxiliary tools and libraries such as documentation

  generation

### Scope

The scope could be anything specifying place of the commit change. For example `engine`, `template`, `clause`, etc...

You can use `*` when the change affects more than a single scope.

### Subject

The subject contains succinct description of the change:

* use the imperative, present tense: "change" not "changed" nor "changes"
* don't capitalize first letter
* no dot \(.\) at the end

### Body

Just as in the **subject**, use the imperative, present tense: "change" not "changed" nor "changes". The body should include the motivation for the change and contrast this with previous behavior.

### Footer

The footer should contain any information about **Breaking Changes** and is also the place to \[reference GitHub issues that this commit closes\]\[closing-issues\].

**Breaking Changes** should start with the word `BREAKING CHANGE:` with a space or two newlines. The rest of the commit message is then used for this.

A detailed explanation can be found in this \[document\]\[commit-message-format\].

##  Writing Documentation

The Ergo project uses [docusaurus](http://docusaurus.io/) for the language documentation.

Code documentation uses the following tools:
- [coq2html](https://github.com/xavierleroy/coq2html) for the compiler specification (install with `opam install coq-coq2html`)
- [odoc](https://github.com/ocaml/odoc) (install with `opam install odoc`)
- [JSDoc](http://usejsdoc.org) for the JavaScript part of the code

This means that all the docs are stored inline in the source code and so are kept in sync as it changes.

This means that since we generate the documentation from the source code, we can easily provide version-specific documentation by simply checking out a version of Ergo and running the build.

## License <a name="license"></a>
Accord Project source code files are made available under the Apache License, Version 2.0 (Apache-2.0), located in the LICENSE file. Accord Project documentation files are made available under the Creative Commons Attribution 4.0 International License (CC-BY-4.0), available at http://creativecommons.org/licenses/by/4.0/.

Copyright 2018 Clause, Inc.


