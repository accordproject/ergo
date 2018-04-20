## What is Ergo?

Ergo is a prototype for a domain specific language (DSL) aimed at
capturing the execution logic of *legal* contracts. It is a work in
progress. Here are some thoughts and notes on requirements and on the
initial design.

## Overview

Ergo is a domain specific language designed to capture the execution
logic of *legal* contracts. Among some of the goals for the language
are:
- to have contracts and clauses as first-class elements of the language
- to help legal-tech developer to quickly and safely develop computable legal contracts
- to be modular, facilitating reuse of existing contract or clause logic
- to ensure safe execution: the language should prevent run-time errors and non-terminating logic
- to be blockchain neutral: the same contract logic can be deployed either on and off chain and to a variety of distributed ledger technologies
- to be formally specified: the meaning of contracts should be well defined so it can be verified, and preserved during execution
- to be consistent with the [Accord Protocol Template Specification](https://docs.google.com/document/d/1UacA_r2KGcBA2D4voDgGE8jqid-Uh4Dt09AE-shBKR0)

## Learning Ergo

The following material is available:

- Ergo Language Manual: [http://ergo.readthedocs.io/en/latest/index.html](http://ergo.readthedocs.io/)
- Ergo Tutorial: [Tutorial.md](Tutorial.md)
- Ergo Formal Specification: [Specification.md](Specification.md)
- Ergo playground: [https://accordproject.github.io/ergo-playground/](https://accordproject.github.io/ergo-playground/)

