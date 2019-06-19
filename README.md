![Ergo](./ergo.png)

![Build Status](https://travis-ci.org/accordproject/ergo.svg?branch=master)
![CircleCI](https://circleci.com/gh/accordproject/ergo.svg?style=shield)
[![Coverage Status](https://coveralls.io/repos/github/accordproject/ergo/badge.svg?branch=master)](https://coveralls.io/github/accordproject/ergo?branch=master)
![lerna](https://img.shields.io/badge/maintained%20with-lerna-cc00ff.svg)
[![npm version](https://badge.fury.io/js/%40accordproject%2Fergo-cli.svg)](https://badge.fury.io/js/%40accordproject%2Fergo-cli)

[Ergo Documentation][docsergo]

## About

This is the source code for the Ergo compiler. Ergo is the [Accord Project][apmain]
language for Smart Legal Contracts.

The Ergo compiler is distributed as an [npm package][npmpkg]. 
If you want to install Ergo, consult the [getting started][getstart] section.

The Ergo compiler is written in [Coq][coq] with a parser and
some support code written in [OCaml][OCaml]. It makes extensive use
of the [Q*cert compiler][Qcertcompiler] for code generation.

Both the Ergo language and its compiler are in early development
phase. If you would like to build from source or to contribute,
consult the [for developers][fordeve] section.

## Try it out

If you want to take a peek at Ergo without installing anything, check
out the interactive [REPL][REPL]
(read-eval-print-loop) for Ergo stand-alone, or the [Accord Project Template Studio][aptempstudio] 
showing how Ergo can express the logic of legal templates.

## Documentation

The most recent documentation for the Ergo language and compiler is
available at the [Ergo documentation][docsergo]

## Getting started

### Install Ergo

The easiest way to install Ergo is as a [Node.js][nodejs] package.
Once you have Node.js installed on your machine, you can get the Ergo compiler
and command-line using the Node.js package manager by typing the following in a
terminal:

```text
$ npm install -g @accordproject/ergo-cli
```

This will install the compiler itself (`ergoc`) and command-line tools (`ergorun` and `ergotop`) to create and invoke Ergo contracts. You can check that both have been installed and print the version number by typing the following in a terminal:

```text
$ ergoc --version
$ ergorun --version
```

Then, to get command line help:

```text
$ ergoc --help
$ ergorun --help
```

### Compiling your first contract

To compile your first Ergo contract to JavaScript:

```text
$ ergoc ./examples/volumediscount/model.cto ./examples/volumediscount/logic.ergo
15:17:08 - info: Logging initialized. 2018-05-24T19:17:08.024Z
Processing file: ./examples/volumediscount/logic.ergo -- compiled to: ./examples/volumediscount/logic.js
```

By default, Ergo compiles to JavaScript for execution. You can inspect
the compiled JavaScript code in `./examples/volumediscount/logic.js`

### Invoke a contract

To compile and execute a contract by sending a request:

```text
$ ergorun execute ./examples/volumediscount/model.cto ./examples/volumediscount/logic.ergo --contract ./examples/volumediscount/contract.json --request ./examples/volumediscount/request.json --state ./examples/volumediscount/state.json
06:40:01 - info:
{
  "response": {
    "discountRate": 2.8,
    "$class": "org.accordproject.volumediscount.VolumeDiscountResponse"
  },
  "state": {
    "$class": "org.accordproject.cicero.contract.AccordContractState",
    "stateId": "1"
  },
  "emit": []
}
```

To compile and invoke a specific contract clause:

```text
$ ergorun invoke ./examples/volumediscount/model.cto ./examples/volumediscount/logic.ergo --clauseName volumediscount --contract ./examples/volumediscount/contract.json --params ./examples/volumediscount/params.json --state ./examples/volumediscount/state.json
06:40:29 - info:
{
  "response": {
    "discountRate": 2.8,
    "$class": "org.accordproject.volumediscount.VolumeDiscountResponse"
  },
  "state": {
    "$class": "org.accordproject.cicero.contract.AccordContractState",
    "stateId": "1"
  },
  "emit": []
}
```

To compile and obtain the initial state for the contract:

```text
$ ergorun init ./examples/volumediscount/model.cto ./examples/volumediscount/logic.ergo --contract ./examples/volumediscount/contract.json
06:40:29 - info:
{
  "response": null,
  "state": {
    "stateId": "org.accordproject.cicero.contract.AccordContractState#1",
    "$class": "org.accordproject.cicero.contract.AccordContractState"
  },
  "emit": []
}
```

## For developers

We welcome contributions. We encourage contributors to consult the following
[Guidelines][contribute]

To setup for development, please consult the [Developer Guide][developer]

Copyright 2018-2019 Clause, Inc.

---

<a href="https://docs.accordproject.org/">
	<img src="assets/APLogo.png" alt="Accord Project Logo" />
</a>

Accord Project is an open source, non-profit, initiative working to transform contract management and contract automation by digitizing contracts.

## Contributing

Read our [contributing guide][contribute] and information for [developers][developer]. Find out what’s coming on our [blog][apblog].

## Getting Started

### Learn About Accord Project
* [Welcome][welcome]
* [Concepts and High-level Architecture][highlevel]
* [Ergo Language][ergolanguage]

### Try Accord Project
* [Using a Template with Cicero][usingcicero]
* [Authoring in Template Studio][authoring]

### Technical Reads
* [Ergo Compiler][ergocompiler]

### Blog
* [Accord Project News][apnews]

### Accord Project Codebase
* [Cicero][cicero]
* [Ergo][ergo]
* [Cicero Template Library][CTL]
* [Models][models]

* [Template Studio][tsv2]
* [Cicero UI][ciceroui]
* [Concerto UI][concertoui]
* [Markdown Editor][mdeditor]

## Community

The Accord Project technology is being developed as open source. All the software packages are being actively maintained on GitHub and we encourage organizations and individuals to contribute requirements, documentation, issues, new templates, and code.

Join the Accord Project Technology Working Group [Slack channel][slack] to get involved!

## License <a name="license"></a>

Accord Project source code files are made available under the [Apache License, Version 2.0][apache].

Accord Project documentation files are made available under the [Creative Commons Attribution 4.0 International License][creativecommons] (CC-BY-4.0).

[docsergo]: https://docs.accordproject.org/docs/ergo.html
[apmain]: https://accordproject.org/ 
[npmpkg]: https://www.npmjs.com/package/@accordproject/ergo-cli
[getstart]: https://docs.accordproject.org/docs/accordproject.html
[coq]: https://coq.inria.fr
[OCaml]: https://ocaml.org
[Qcertcompiler]: https://querycert.github.io
[fordeve]: https://docs.accordproject.org/docs/ref-logic.html
[REPL]: https://ergorepl.netlify.com
[aptempstudio]: https://studio.accordproject.org
[nodejs]: https://nodejs.org/

[apspec]: https://docs.accordproject.org/docs/cicero-specification.html
[apworkgroup]: https://calendar.google.com/calendar/event?action=TEMPLATE&tmeid=MjZvYzIzZHVrYnI1aDVzbjZnMHJqYmtwaGlfMjAxNzExMTVUMjEwMDAwWiBkYW5AY2xhdXNlLmlv&tmsrc=dan%40clause.io

[contribute]: https://github.com/accordproject/ergo/blob/master/CONTRIBUTING.md
[developer]: https://github.com/accordproject/ergo/blob/master/DEVELOPERS.md
[apblog]: https://medium.com/@accordhq

[welcome]: https://docs.accordproject.org/docs/accordproject.html#what-is-accord-project
[highlevel]: https://docs.accordproject.org/docs/spec-concepts.html
[ergolanguage]: https://docs.accordproject.org/docs/logic-ergo.html

[usingcicero]: https://docs.accordproject.org/docs/basic-use.html
[authoring]: https://docs.accordproject.org/docs/advanced-latedelivery.html

[ergocompiler]: https://docs.accordproject.org/docs/ref-logic-specification.html

[apnews]: https://www.accordproject.org/news/
[cicero]: https://github.com/accordproject/cicero
[ergo]: https://github.com/accordproject/ergo
[CTL]: https://github.com/accordproject/cicero-template-library
[models]: https://github.com/accordproject/models

[tsv2]: https://github.com/accordproject/template-studio-v2
[ciceroui]: https://github.com/accordproject/cicero-ui
[concertoui]: https://github.com/accordproject/concerto-ui
[mdeditor]: https://github.com/accordproject/markdown-editor

[slack]: https://accord-project-slack-signup.herokuapp.com
[apache]: https://github.com/accordproject/ergo/blob/master/LICENSE
[creativecommons]: http://creativecommons.org/licenses/by/4.0/