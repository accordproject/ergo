# Developing Ergo
 
* [Development Setup][developers.setup]
* [Coding Rules][developers.rules]
* [Commit Message Guidelines][developers.commits]
* [Writing Documentation][developers.documentation]

## Overview

This document describes how to set up your development environment to build and test Ergo, and explains the basic mechanics of using `git`, `node`, `lerna`.

The core of the Ergo compiler is extracted from a formal specification in Coq to JavaScript.

The code is located in the following directories:

* in `mechanization` the Coq code (includes the abstract syntax tree, intermediate languages, and compiler to JavaScript)
* in `extraction` support code in OCaml (includes the parser)
* in `packages` the JavaScript packages, containing the Ergo compiler API and command-line tools

## <a name="setup"> Development Setup

### Installing Prerequisites

Before you can build Ergo, you must install and configure the following prerequisites on your machine:

* [Git](http://git-scm.com/): The [Github Guide to Installing Git][git-setup] is a good source of information.
* [Node.js v8.x \(LTS\)](http://nodejs.org): We use Node to generate the documentation, run a development web server, run tests, and generate distributable files. Depending on your system, you can install Node either from the source or as a pre-packaged bundle.

We recommend using [nvm](https://github.com/creationix/nvm) (or [nvm-windows](https://github.com/coreybutler/nvm-windows)) to manage and install Node.js, which makes it easy to change the version of Node.js per project.

* [Lerna](https://lerna.js.org): We use lerna to handle multiple npm packages in the Ergo repository. To install:

```sh
$ npm install -g lerna@^3.15.0
```

* [opam](https://opam.ocaml.org): the OCaml package manager, for OCaml 4.07.1. To install:

```sh
$ sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
$ eval $(opam env)
$ opam switch create 4.07.1
```

### Forking Ergo on Github

To contribute code to Ergo, you must have a GitHub account so you can push code to your own fork of Ergo and open Pull Requests in the [GitHub Repository][github].

To create a Github account, follow the instructions [here](https://github.com/signup/free). Afterwards, go ahead and [fork](http://help.github.com/forking) the [main Ergo repository][github].

### Install development version

To install the latest development code, clone this git repository and do a local install:

```sh
$ git clone https://github.com/accordproject/ergo.git
$ cd ./ergo/packages/ergo-cli
$ npm install -g
```

#### Dependencies

To rebuild the compiler from the source, you will need Coq 8.8.2 and OCaml 4.07.1 with some additional libraries. You can add the necessary libraries with opam as follow:
 
```sh
$ opam repo add coq-released https://coq.inria.fr/opam/released
$ opam install ocamlbuild menhir camlp5 base64 js_of_ocaml js_of_ocaml-ppx yojson atdgen re calendar uri
$ opam install coq.8.8.2 coq-qcert.1.4.1
```

#### Build the Ergo Compiler and REPL

To recompile Ergo from its source, do:

```sh
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

We write unit and integration tests with Mocha and Cucumber. To run all of the tests once run:

```text
lerna run test
```

## <a name="rules"></a> Coding Rules

To ensure consistency throughout the source code, keep these rules in mind as you are working:

* All features or bug fixes **must be tested** by one or more [specs][developers.unit-tests].
* All public API methods **must be documented** with jsdoc. To see how we document our APIs, please check
 out the existing source code and see the section about [writing documentation][developers.documentation]
* With the exceptions listed below, we follow the rules contained in
 [Google's JavaScript Style Guide][google].

## <a name="commits"></a> Git Commit Guidelines

We have very precise rules over how our git commit messages can be formatted.  This leads to **more
readable messages** that are easy to follow when looking through the **project history** and **git logs**. 
But also, we use the git commit messages to **generate the Ergo change log**.

The commit message formatting can be added using a version of typical git workflow.

### Commit Message Format
Each commit message consists of a mandatory **type**, **scope**, **subject**, and **footer**. This is a specific format:

```shell
   <type>(<scope>): <subject> - <footer>
```

This allows the message to be easier to read on GitHub as well as in various git tools.

### Revert
If the commit reverts a previous commit, it should begin with `revert: `, followed by the subject, where it
should say: `this reverts commit <hash>.`, where the hash is the SHA of the commit being reverted.
A commit with this format is automatically created by the `git revert` command.

### Type
Must be one of the following:

* **`feat`**: A new feature
* **`fix`**: A bug fix
* **`docs`**: Documentation only changes
* **`style`**: Changes that do not affect the meaning of the code (white-space, formatting, missing
 semi-colons, etc)
* **`refactor`**: A code change that neither fixes a bug nor adds a feature
* **`perf`**: A code change that improves performance
* **`test`**: Adding missing or correcting existing tests
* **`chore`**: Changes to the build process or auxiliary tools and libraries such as documentation
 generation

### Scope
The scope will be specifying the place of the commit change; the focal point of new code or best
description of where changes can be found.

You can use `*` when the change affects more than a single scope.

### Subject
The subject contains a succinct description of the change:

* use the imperative, present tense: "change" not "changed" nor "changes"
* don't capitalize the first letter
* kept under 50 characters
* no dot (.) at the end

### Footer
The footer should contain [reference GitHub Issues][github-issues] that this commit addresses.

## <a name="pullrequests"></a> GitHub Pull Request Guidelines
Pull Requests should consist of a complete addition to the code which contains value.
Because the commits inside follow a pattern, the title should be an extension or summary of all the commits inside.

Pull Request titles should follow [commit message formatting][developers.commits].

Formatting for the body is displayed in this example:

```shell
# Issue #20

### Changes
- Change one
 - Subchange one
 - Subchange two
- Change two
- Theoretically, this should be listing all the commit messages included in this PR

### Flags
- Possible issues or holds for reviewers to note
- List any breaking changes here.

### Related Issues
- Link any issues or pull requests relating to this
```

When approved and ready to merge, a Pull Request should be squashed down to a single buildable commit and merged into master.

##  Writing Documentation

The Ergo project uses [Docusaurus][docusaurus] for the language documentation.

Code documentation uses the following tools:
- [coq2html][coq2html] for the compiler specification (install with `opam install coq-coq2html`)
- [odoc][odoc] (install with `opam install odoc`)
- [JSDoc][jsdoc] for the JavaScript part of the code

This means that all the docs are stored inline in the source code and so are kept in sync as it changes.

This means that since we generate the documentation from the source code, we can easily provide version-specific documentation by simply checking out a version of Ergo and running the build.

## License <a name="license"></a>

Accord Project source code files are made available under the [Apache License, Version 2.0][apache].

Accord Project documentation files are made available under the [Creative Commons Attribution 4.0 International License][creativecommons] (CC-BY-4.0).

Copyright 2018-2019 Clause, Inc.

[developers.setup]: DEVELOPERS.md#setup
[developers.rules]: DEVELOPERS.md#rules
[developers.commits]: DEVELOPERS.md#commits
[developers.documentation]: DEVELOPERS.md#documentation
[developers.unit-tests]: DEVELOPERS.md#unit-tests

[git]: http://git-scm.com/
[git-setup]: https://help.github.com/en/articles/set-up-git
[node]: https://nodejs.org/en/
[nvm]: https://github.com/creationix/nvm
[nvm-windows]: https://github.com/coreybutler/nvm-windows
[github]: https://github.com/accordproject/ergo
[github-signup]: https://github.com/signup/free
[github-issues]: https://github.com/accordproject/ergo/issues
[github-forking]: http://help.github.com/forking
[google]: https://google.github.io/styleguide/jsguide.html
[commit]: https://github.com/commitizen/cz-cli

[docusaurus]: http://docusaurus.io/
[coq2html]: https://github.com/xavierleroy/coq2html
[odoc]: https://github.com/ocaml/odoc
[jsdoc]: http://usejsdoc.org/

[apache]: https://github.com/accordproject/ergo/blob/master/LICENSE
[creativecommons]: http://creativecommons.org/licenses/by/4.0/

