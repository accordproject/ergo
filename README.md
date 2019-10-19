<p align="center">
  <a href="./ergo.png">
    <img src="./ergo.png" alt="Ergo logo">
  </a>
</p>

![Build Status](https://travis-ci.org/accordproject/ergo.svg?branch=master)
![CircleCI](https://circleci.com/gh/accordproject/ergo.svg?style=shield)
[![Coverage Status](https://coveralls.io/repos/github/accordproject/ergo/badge.svg?branch=master)](https://coveralls.io/github/accordproject/ergo?branch=master)
[![GitHub license](https://img.shields.io/github/license/accordproject/ergo?color=bright-green)](https://github.com/accordproject/ergo/blob/master/LICENSE)
[![downloads](https://img.shields.io/npm/dm/@accordproject/ergo-cli)](https://www.npmjs.com/package/@accordproject/ergo-cli)
[![npm version](https://badge.fury.io/js/%40accordproject%2Fergo-cli.svg)](https://badge.fury.io/js/%40accordproject%2Fergo-cli)
![lerna](https://img.shields.io/badge/maintained%20with-lerna-cc00ff.svg)
[![Netlify Status](https://api.netlify.com/api/v1/badges/8b6ef766-c6d0-45bb-bff6-03104e6ff913/deploy-status)](https://app.netlify.com/sites/ergorepl/deploys)
[![Join the Accord Project Slack](https://img.shields.io/badge/Accord%20Project-Join%20Slack-blue)](https://accord-project-slack-signup.herokuapp.com/)

## About

This is the source code for the Ergo compiler. Ergo is the [Accord Project][apmain]
language for Smart Legal Contracts.

The Ergo compiler is distributed as an [npm package][npmpkg]. 

The Ergo compiler is written using the [Coq][coq] proof assistant, with parsing and
support code written in [OCaml][OCaml]. It makes extensive use
of the [Q*cert compiler][Qcert] for code generation and type checking.

Both the Ergo language and its compiler are in early development
phase. If you would like to build from source or to contribute,
consult the [DEVELOPERS][developers] file.

## Try Ergo online

If you want to take a peek at Ergo without installing anything, check
out the interactive [REPL][REPL]
(read-eval-print-loop) for Ergo stand-alone, or the [Accord Project Template Studio][studio] 
which illustrates Ergo in Accord Project templates.

## Documentation

The most recent Ergo documentation is in the [Ergo Language Guide][docergo].

## Quickstart

### Install Ergo

The easiest way to install Ergo is as a [Node.js][nodejs] package.
Once you have Node.js installed on your machine, you can get the Ergo compiler
and command-line using the Node.js package manager by typing the following in a
terminal:

```sh
$ npm install -g @accordproject/ergo-cli
```

This will install the Ergo command-line (`ergo`) and Read-Eval-Print-Loop (`ergotop`). Those will allow you to create, test and compile Ergo contracts. You can check your installed version by typing the following in a terminal:

```sh
$ ergo --version
```

Or to get command line help:

```sh
$ ergo --help
ergo <command>

Commands:
  ergo draft       create a contract text from data
  ergo execute     send a request to the contract
  ergo invoke      invoke a clause of the contract
  ergo initialize  initialize the state for a contract
  ergo compile     compile a contract

Options:
  --help         Show help                                             [boolean]
  --version      Show version number                                   [boolean]
  --verbose, -v                                                 [default: false]
```

### Create contract text

To create a contract text from a contract:

```sh
$ ergo draft --template ./examples/volumediscount --data ./examples/volumediscount/data.json
```

### Initialize a contract

To obtain the initial state of the contract:

```sh
$ ergo initialize --template ./examples/volumediscount --data ./examples/volumediscount/data.json
06:40:29 - info:
```

### Send a request to a contract

To send a request to a contract:

```sh
$ ergo execute --template ./examples/volumediscount --data ./examples/volumediscount/data.json --request ./examples/volumediscount/request.json --state ./examples/volumediscount/state.json
06:40:01 - info:
{
  "clause": "orgXaccordprojectXvolumediscountXVolumeDiscount",
  "request": {
    "$class": "org.accordproject.volumediscount.VolumeDiscountRequest",
    "netAnnualChargeVolume": 10.4
  },
  "response": {
    "$class": "org.accordproject.volumediscount.VolumeDiscountResponse",
    "discountRate": 2.8,
    "transactionId": "13fa7cb6-03fc-4fd8-8e12-9a85ac8d5eb7",
    "timestamp": "2019-10-12T23:56:33.688Z"
  },
  "state": {
    "$class": "org.accordproject.cicero.contract.AccordContractState",
    "stateId": "1"
  },
  "emit": []
}
```

### Invoke a clause

To invoke a specific clause of the contract:

```sh
$ ergo invoke --template ./examples/volumediscount --clauseName volumediscount --data ./examples/volumediscount/data.json --params ./examples/volumediscount/params.json --state ./examples/volumediscount/state.json
```

### Compile a contract

To compile your first Ergo contract to JavaScript:

```sh
$ ergo compile ./examples/volumediscount/model/model.cto ./examples/volumediscount/logic/logic.ergo
Processing file: ./examples/volumediscount/logic.ergo -- compiled to: ./examples/volumediscount/logic.js
```

By default, Ergo compiles to JavaScript for execution. You can inspect
the compiled JavaScript code in `./examples/volumediscount/logic.js`

---

<p align="center">
  <a href="https://www.accordproject.org/">
    <img src="assets/APLogo.png" alt="Accord Project Logo" width="400" />
  </a>
</p>

Accord Project is an open source, non-profit, initiative working to transform contract management and contract automation by digitizing contracts. Accord Project operates under the umbrella of the [Linux Foundation][linuxfound]. The technical charter for the Accord Project can be found [here][charter].

## Learn More About Accord Project

### Overview
* [Accord Project][apmain]
* [Accord Project News][apnews]
* [Accord Project Blog][apblog]
* [Accord Project Slack][apslack]
* [Accord Project Technical Documentation][apdoc]
* [Accord Project GitHub][apgit]


### Documentation
* [Getting Started with Accord Project][docwelcome]
* [Concepts and High-level Architecture][dochighlevel]
* [How to use the Cicero Templating System][doccicero]
* [How to Author Accord Project Templates][docstudio]
* [Ergo Language Guide][docergo]

### Ecosystem


#### Core libraries:
<table>
  <tr>
    <th headers="blank">Projects</th>
    <th headers="blank">Package name</th>
    <th headers="blank">Version</th>
    <th headers="blank">Description</th>
  </tr>
  <tr>
    <td headers><a href="https://github.com/accordproject/cicero">Cicero</a></td>
    <td headers> <a href="https://github.com/accordproject/cicero/tree/master/packages/cicero-core">cicero-core</a></td>
    <td headers> <a href="https://badge.fury.io/js/%40accordproject%2Fcicero-core"><img src="https://badge.fury.io/js/%40accordproject%2Fcicero-core.svg" alt="npm version"></a></td>
    <td headers>Templates Core</td>
  </tr>
    <tr>
      <td headers></td>
    <td headers> <a href="https://github.com/accordproject/cicero/tree/master/packages/cicero-cli">cicero-cli</a></td>
      <td headers> <a href="https://badge.fury.io/js/%40accordproject%2Fcicero-cli"><img src="https://badge.fury.io/js/%40accordproject%2Fcicero-cli.svg" alt="npm version"></a></td>
      <td headers> Cicero CLI </td>
    </tr>
    <tr>
    <td headers></td>
    <td headers> <a href="https://github.com/accordproject/cicero/tree/master/packages/cicero-engine">cicero-engine</a></td>
    <td headers> <a href="https://badge.fury.io/js/%40accordproject%2Fcicero-engine"><img src="https://badge.fury.io/js/%40accordproject%2Fcicero-engine.svg" alt="npm version"></a></td>
    <td headers>Node.js VM based implementation of Accord Protcol Template Specification execution</td>
    </tr>
    <tr>
    <td headers></td>
    <td headers> <a href="https://github.com/accordproject/cicero/tree/master/packages/cicero-server">cicero-server</a></td>
    <td headers> <a href="https://badge.fury.io/js/%40accordproject%2Fcicero-server"><img src="https://badge.fury.io/js/%40accordproject%2Fcicero-server.svg" alt="npm version"></a></td>
    <td headers>Wraps the Cicero Engine and exposes it as a RESTful service<td>
    </tr>
    <tr>
    <td headers></td>
    <td headers> <a href="https://github.com/accordproject/cicero/tree/master/packages/cicero-test">cicero-test</a></td>
    <td headers> <a href="https://badge.fury.io/js/%40accordproject%2Fcicero-test"><img src="https://badge.fury.io/js/%40accordproject%2Fcicero-test.svg" alt="npm version"></a></td>
    <td headers> Testing support for Cicero based on cucumber</td>
    </tr>
     <tr>
     <td headers></td>
     <td headers> <a href="https://github.com/accordproject/cicero/tree/master/packages/cicero-tools">cicero-tools</a></td>
     <td headers> <a href="https://badge.fury.io/js/%40accordproject%2Fcicero-tools"><img src="https://badge.fury.io/js/%40accordproject%2Fcicero-tools.svg" alt="npm version"></a></td>
     <td headers>Cicero Tools</td>
     </tr>
      <tr>
      <td headers="co1 c1"></td>
      <td headers="co2 c1"> <a href="https://github.com/accordproject/cicero/tree/master/packages/generator-cicero-template">generator-cicero-template</a></td>
      <td headers="co3 c1"> <a href="https://badge.fury.io/js/%40accordproject%2Fgenerator-cicero-template"><img src="https://badge.fury.io/js/%40accordproject%2Fgenerator-cicero-template.svg" alt="npm version"></a></td>
      <td headers="co4 c1">Code generator for a Cicero Template</td>
      </tr>
      <tr>
      <td headers><a href="https://github.com/accordproject/concerto">Concerto</a></td>
      <td headers><a href="https://github.com/accordproject/concerto/tree/master/packages/concerto-core">concerto-core</a></td>
      <td headers> <a href="https://badge.fury.io/js/%40accordproject%2Fconcerto-core"><img src="https://badge.fury.io/js/%40accordproject%2Fconcerto-core.svg" alt="npm version"></a></td>
      <td headers> Core Implementation for the Concerto Modeling Language</td>
      </tr>
      <tr>
      <td headers></td>
      <td headers><a href="https://github.com/accordproject/concerto/tree/master/packages/concerto-tools">concerto-tools</a></td>
      <td headers> <a href="https://badge.fury.io/js/%40accordproject%2Fconcerto-tools"><img src="https://badge.fury.io/js/%40accordproject%2Fconcerto-tools.svg" alt="npm version"></a></td>
      <td headers> Tools for the Concerto Modeling Language</td>
  </tr>
  <tr>
   <td headers></td>
   <td headers><a href="https://github.com/accordproject/concerto/tree/master/packages/concerto-cli">concerto-cli</a></td>
   <td headers> <a href="https://badge.fury.io/js/%40accordproject%2Fconcerto-cli"><img src="https://badge.fury.io/js/%40accordproject%2Fconcerto-cli.svg" alt="npm version"></a></td>
   <td headers>command-line interface for Concerto</td>
  </tr>
  <tr>
    <td headers><a href="https://github.com/accordproject/ergo">Ergo</a></td>
    <td headers><a href="https://github.com/accordproject/ergo/tree/master/packages/ergo-cli">ergo-cli</a></td>
    <td headers><a href="https://badge.fury.io/js/%40accordproject%2Fergo-cli"><img src="https://badge.fury.io/js/%40accordproject%2Fergo-cli.svg" alt="npm version"></a></td>
    <td headers>Ergo CLI</td>
  </tr>
  <tr>
    <th id="blank"></th>
    <td headers><a href="https://github.com/accordproject/ergo/tree/master/packages/ergo-compiler">ergo-compiler</a></td>
    <td headers><a href="https://badge.fury.io/js/%40accordproject%2Fergo-compiler"><img src="https://badge.fury.io/js/%40accordproject%2Fergo-compiler.svg" alt="npm version"></a></td>
    <td headers>Ergo compiler</td>
  </tr>
  <tr>
   <th id="blank"></th>
   <td headers><a href="https://github.com/accordproject/ergo/tree/master/packages/ergo-test">ergo-test</a></td>
   <td headers><a href="https://badge.fury.io/js/%40accordproject%2ergo-test"><img src="https://badge.fury.io/js/%40accordproject%2Fergo-test.svg" alt="npm version"></a></td>
   <td headers>Ergo test</td>
   </tr>
    <tr>
    <th id="blank"></th>
    <td headers><a href="https://github.com/accordproject/ergo/tree/master/packages/ergo-engine">ergo-engine</a></td>
    <td headers><a href="https://badge.fury.io/js/%40accordproject%2Fergo-engine"><img src="https://badge.fury.io/js/%40accordproject%2Fergo-engine.svg" alt="npm version"></a></td>
    <td headers>Ergo engine</td>
    </tr>
    <tr>
     <td headers><a href="https://docs.accordproject.org/docs/next/markup-cicero.html">Markdown</a></td>
     <td headers><a href="https://github.com/accordproject/markdown-transform/tree/master/packages/markdown-common">markdown-common</a></td>
     <td headers><a href="https://badge.fury.io/js/%40accordproject%2Fmarkdown-common"><img src="https://badge.fury.io/js/%40accordproject%2Fmarkdown-common.svg" alt="npm version"></a></td>
     <td headers>A framework for transforming markdown</td>
    </tr>
     <tr>
     <th id="blank"></th>
     <td headers><a href="https://github.com/accordproject/markdown-transform/tree/master/packages/markdown-slate">markdown-slate</a></td>
     <td headers><a href="https://badge.fury.io/js/%40accordproject%2Fmarkdown-slate"><img src="https://badge.fury.io/js/%40accordproject%2Fmarkdown-slate.svg" alt="npm version"></a></td>
     <td headers>Transform markdown to/from CommonMark DOM</td>
     </tr>
     <tr>
     <td headers></td>
     <td headers><a href="https://github.com/accordproject/markdown-transform/tree/master/packages/markdown-cli"> markdown-cli </a></td>
     <td headers> <a href="https://badge.fury.io/js/%40accordproject%2Fmarkdown-cli"><img src="https://badge.fury.io/js/%40accordproject%2Fmarkdown-cli.svg" alt="npm version"></a></td>
     <td headers> CLI for markdown transformations.</td>
    </tr>
     <tr>
      <th id="blank"></th>
      <td headers><a href="https://github.com/accordproject/markdown-transform/tree/master/packages/markdown-cicero">markdown-cicero</a></td>
      <td headers><a href="https://badge.fury.io/js/%40accordproject%2Fmarkdown-cicero"><img src="https://badge.fury.io/js/%40accordproject%2Fmarkdown-cicero.svg" alt="npm version"></a></td>
      <td headers>CiceroDOM: Markdown extensions for contracts, clauses, variables etc.</td>
      </tr>
       <tr>
      <th id="blank"></th>
       <td headers><a href="https://github.com/accordproject/markdown-transform/tree/master/packages/markdown-html">markdown-html</a></td>
       <td headers><a href="https://badge.fury.io/js/%40accordproject%2Fmarkdown-html"><img src="https://badge.fury.io/js/%40accordproject%2Fmarkdown-html.svg" alt="npm version"></a></td>
       <td headers>Transform CiceroDOM to HTML</td>
       </tr>
 
</table>

#### UI Components:

<table>
  <tr>
    <th  headers="blank">Projects</th>
    <th  headers="blank">Package name</th>
    <th  headers="blank">Version</th>
    <th  headers="blank">Description</th>
  </tr>
    <tr>
      <td headers>Markdown Editor</td>
      <td headers><a href="https://github.com/accordproject/markdown-editor">markdown-editor</a></td>
      <td headers><img src="https://badge.fury.io/js/%40accordproject%2Fmarkdown-editor.svg" alt="npm version"></a></td>
      <td headers>WYSIWYG rich text web editor that persists text as markdown. Based on Slate.js</td>
    </tr>
     <tr>
     <td headers="co1 c1">Cicero UI</td>
      <td headers="co2 c1"><a href="https://github.com/accordproject/cicero-ui">cicero-ui</a></td>
      <td headers="co3 c1"> <a href="https://badge.fury.io/js/%40accordproject%2Fcicero-ui"><img src="https://badge.fury.io/js/%40accordproject%2Fcicero-ui.svg" alt="npm version"></a></td>
       <td headers="co4 c1">WYSIWYG contract editor, template libary browser, error panel component</td>
     </tr>
     <tr>
     <td headers="co1 c1">Concerto UI</td>
      <td headers="co2 c1"><a href="https://github.com/accordproject/concerto-ui">concerto-ui</a></td>
      <td headers="co3 c1"> <a href="https://badge.fury.io/js/%40accordproject%2Fconcerto-ui-react"><img src="https://badge.fury.io/js/%40accordproject%2Fconcerto-ui-react.svg" alt="npm version"></a></td>
       <td headers="co4 c1">Dynamic web forms generated from Concerto models</td>
     </tr>
</table>
  

#### Template Editors:

<table>
  <tr>
    <th headers="blank">Projects</th>
    <th headers="blank">Cicero ver.</th>
    <th headers="blank">Description</th>
  </tr>
  <tr>
    <td headers><a href="https://github.com/accordproject/template-studio">Template Studio v1</a></td>
    <td headers> <b>0.13.4</b></td>
    <td headers>Web UI for creating, editing and testing Accord Project templates</td>
  </tr>
  <tr>
    <td headers><a href="https://github.com/accordproject/template-studio-v2">Template Studio v2</a></td>
    <td headers> <b>0.13.4</b></td>
    <td headers>Web UI for creating, editing and testing Accord Project templates</td>
  </tr>
   <tr>
    <td headers><a href="https://github.com/accordproject/cicero-vscode-extension">VSCode Extension</a></td>
    <td headers><b>0.13.4</b></td>
    <td headers>VS Code extension for editing Cicero templates and Ergo logic</td>
   </tr>
</table>


#### Public templates and models:

<table>
  <tr>
    <th headers="blank">Projects</th>
    <th headers="blank">Description</th>
  </tr>
  <tr>
    <td headers><a href="https://github.com/accordproject/models">Models</a></td>
    <td headers>Accord Project Model Library </td>
  </tr>
   <tr>
     <td headers><a href="https://github.com/accordproject/cicero-template-library">Template Library</a></td>
     <td headers>Accord Project Template Library </td>
   </tr>
 
</table>


#### Documentation:

<table>
  <tr>
    <th headers="blank">Project</th>
    <th headers="blank">Repo</th>
  </tr>
  <tr>
    <td headers><a href="https://docs.accordproject.org/">Documentation</a></td>
    <td headers><a href="https://github.com/accordproject/techdocs">techdocs</a></td>
  </tr>
 </table>

## Contributing

The Accord Project technology is being developed as open source. All the software packages are being actively maintained on GitHub and we encourage organizations and individuals to contribute requirements, documentation, issues, new templates, and code.

Find out what’s coming on our [blog][apblog].

Join the Accord Project Technology Working Group [Slack channel][apslack] to get involved!

For code contributions, read our [CONTRIBUTING guide][contributing] and information for [DEVELOPERS][developers].

## Contributors ✨

Thanks goes to these wonderful people ([emoji key](https://allcontributors.org/docs/en/emoji-key)):

<!-- ALL-CONTRIBUTORS-LIST:START - Do not remove or modify this section -->
<!-- prettier-ignore-start -->
<!-- markdownlint-disable -->
<table>
  <tr>
    <td align="center"><a href="https://github.com/jeromesimeon"><img src="https://avatars0.githubusercontent.com/u/670099?v=4" width="100px;" alt="Jerome Simeon"/><br /><sub><b>Jerome Simeon</b></sub></a><br /><a href="https://github.com/accordproject/ergo/commits?author=jeromesimeon" title="Code">💻</a></td>
    <td align="center"><a href="https://cs.stanford.edu/~kach/"><img src="https://avatars3.githubusercontent.com/u/5202416?v=4" width="100px;" alt="Kartik Chandra"/><br /><sub><b>Kartik Chandra</b></sub></a><br /><a href="https://github.com/accordproject/ergo/commits?author=kach" title="Code">💻</a></td>
    <td align="center"><a href="http://jolenelanglinais.com"><img src="https://avatars3.githubusercontent.com/u/36460856?v=4" width="100px;" alt="Jolene Langlinais"/><br /><sub><b>Jolene Langlinais</b></sub></a><br /><a href="https://github.com/accordproject/ergo/commits?author=irmerk" title="Code">💻</a></td>
    <td align="center"><a href="http://clause.io"><img src="https://avatars1.githubusercontent.com/u/7544022?v=4" width="100px;" alt="Matt Roberts"/><br /><sub><b>Matt Roberts</b></sub></a><br /><a href="https://github.com/accordproject/ergo/commits?author=mttrbrts" title="Code">💻</a></td>
    <td align="center"><a href="https://github.com/jbesq777"><img src="https://avatars0.githubusercontent.com/u/3835594?v=4" width="100px;" alt="Joseph J Bambara"/><br /><sub><b>Joseph J Bambara</b></sub></a><br /><a href="https://github.com/accordproject/ergo/commits?author=jbesq777" title="Code">💻</a></td>
    <td align="center"><a href="https://github.com/dselman"><img src="https://avatars0.githubusercontent.com/u/623108?v=4" width="100px;" alt="Dan Selman"/><br /><sub><b>Dan Selman</b></sub></a><br /><a href="https://github.com/accordproject/ergo/commits?author=dselman" title="Code">💻</a></td>
    <td align="center"><a href="http://www.clause.io"><img src="https://avatars1.githubusercontent.com/u/9304034?v=4" width="100px;" alt="Peter Hunn"/><br /><sub><b>Peter Hunn</b></sub></a><br /><a href="https://github.com/accordproject/ergo/commits?author=peterhunn" title="Code">💻</a></td>
  </tr>
  <tr>
    <td align="center"><a href="https://twitter.com/PetrGazarov"><img src="https://avatars3.githubusercontent.com/u/5581195?v=4" width="100px;" alt="Petr Gazarov"/><br /><sub><b>Petr Gazarov</b></sub></a><br /><a href="https://github.com/accordproject/ergo/commits?author=petrgazarov" title="Code">💻</a></td>
    <td align="center"><a href="http://www.gargarchit.ga"><img src="https://avatars3.githubusercontent.com/u/42545374?v=4" width="100px;" alt="Archit"/><br /><sub><b>Archit</b></sub></a><br /><a href="https://github.com/accordproject/ergo/commits?author=gargarchit" title="Code">💻</a></td>
    <td align="center"><a href="https://github.com/aayushbisen"><img src="https://avatars2.githubusercontent.com/u/41341387?v=4" width="100px;" alt="Aayush Bisen"/><br /><sub><b>Aayush Bisen</b></sub></a><br /><a href="https://github.com/accordproject/ergo/commits?author=aayushbisen" title="Code">💻</a></td>
    <td align="center"><a href="https://github.com/michizhou"><img src="https://avatars3.githubusercontent.com/u/33012425?v=4" width="100px;" alt="michizhou"/><br /><sub><b>michizhou</b></sub></a><br /><a href="https://github.com/accordproject/ergo/commits?author=michizhou" title="Code">💻</a></td>
    <td align="center"><a href="https://github.com/Parikshit-Hooda"><img src="https://avatars1.githubusercontent.com/u/25405707?v=4" width="100px;" alt="Parikshit Hooda"/><br /><sub><b>Parikshit Hooda</b></sub></a><br /><a href="https://github.com/accordproject/ergo/commits?author=Parikshit-Hooda" title="Code">💻</a></td>
    <td align="center"><a href="https://github.com/RanadeepPolavarapu"><img src="https://avatars1.githubusercontent.com/u/7084995?v=4" width="100px;" alt="RanadeepPolavarapu"/><br /><sub><b>RanadeepPolavarapu</b></sub></a><br /><a href="https://github.com/accordproject/ergo/commits?author=RanadeepPolavarapu" title="Code">💻</a></td>
    <td align="center"><a href="https://arshadkazmi42.github.io/"><img src="https://avatars3.githubusercontent.com/u/4654382?v=4" width="100px;" alt="Arshad Kazmi"/><br /><sub><b>Arshad Kazmi</b></sub></a><br /><a href="https://github.com/accordproject/ergo/commits?author=arshadkazmi42" title="Code">💻</a></td>
  </tr>
  <tr>
    <td align="center"><a href="https://twitter.com/daniloff200"><img src="https://avatars1.githubusercontent.com/u/13692220?v=4" width="100px;" alt="Dmitriy Danilov"/><br /><sub><b>Dmitriy Danilov</b></sub></a><br /><a href="https://github.com/accordproject/ergo/commits?author=daniloff200" title="Code">💻</a></td>
    <td align="center"><a href="https://kewbish.github.io"><img src="https://avatars1.githubusercontent.com/u/45278276?v=4" width="100px;" alt="Kewbish"/><br /><sub><b>Kewbish</b></sub></a><br /><a href="https://github.com/accordproject/ergo/commits?author=kewbish" title="Code">💻</a></td>
    <td align="center"><a href="https://github.com/alvesgabriel"><img src="https://avatars3.githubusercontent.com/u/12446314?v=4" width="100px;" alt="Gabriel Alves"/><br /><sub><b>Gabriel Alves</b></sub></a><br /><a href="https://github.com/accordproject/ergo/commits?author=alvesgabriel" title="Code">💻</a></td>
  </tr>
</table>

<!-- markdownlint-enable -->
<!-- prettier-ignore-end -->
<!-- ALL-CONTRIBUTORS-LIST:END -->

This project follows the [all-contributors](https://github.com/all-contributors/all-contributors) specification. Contributions of any kind welcome!

## License <a name="license"></a>

Accord Project source code files are made available under the [Apache License, Version 2.0][apache].
Accord Project documentation files are made available under the [Creative Commons Attribution 4.0 International License][creativecommons] (CC-BY-4.0).

Copyright 2018-2019 Clause, Inc. All trademarks are the property of their respective owners. See [LF Projects Trademark Policy](https://lfprojects.org/policies/trademark-policy/).

[apmain]: https://accordproject.org/ 
[apworkgroup]: https://calendar.google.com/calendar/event?action=TEMPLATE&tmeid=MjZvYzIzZHVrYnI1aDVzbjZnMHJqYmtwaGlfMjAxNzExMTVUMjEwMDAwWiBkYW5AY2xhdXNlLmlv&tmsrc=dan%40clause.io
[apblog]: https://medium.com/@accordhq
[apnews]: https://www.accordproject.org/news/
[apgit]:  https://github.com/accordproject/
[apdoc]: https://docs.accordproject.org/
[apslack]: https://accord-project-slack-signup.herokuapp.com

[docspec]: https://docs.accordproject.org/docs/spec-overview.html
[docwelcome]: https://docs.accordproject.org/docs/accordproject.html
[dochighlevel]: https://docs.accordproject.org/docs/spec-concepts.html
[docergo]: https://docs.accordproject.org/docs/logic-ergo.html
[docstart]: https://docs.accordproject.org/docs/accordproject.html
[doccicero]: https://docs.accordproject.org/docs/basic-use.html
[docstudio]: https://docs.accordproject.org/docs/advanced-latedelivery.html

[contributing]: https://github.com/accordproject/ergo/blob/master/CONTRIBUTING.md
[developers]: https://github.com/accordproject/ergo/blob/master/DEVELOPERS.md

[linuxfound]: https://www.linuxfoundation.org
[charter]: https://github.com/accordproject/ergo/blob/master/CHARTER.md
[npmpkg]: https://www.npmjs.com/package/@accordproject/ergo-cli
[coq]: https://coq.inria.fr
[OCaml]: https://ocaml.org
[Qcert]: https://querycert.github.io
[REPL]: https://ergorepl.netlify.com
[studio]: https://studio.accordproject.org
[nodejs]: https://nodejs.org/

[apache]: https://github.com/accordproject/ergo/blob/master/LICENSE
[creativecommons]: http://creativecommons.org/licenses/by/4.0/
