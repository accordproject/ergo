---
id: ergo-overview
title: Overview
---

Ergo is a prototype for a domain specific language (DSL) aimed at capturing the execution logic of *legal* contracts. The basic idea of a DSL is a computer language that's targeted to a particular kind of problem, rather than a general-purpose language that's aimed at any kind of software problem. For example, HTML is a DSL targeted at developing web pages. So, Ergo is a DSL aimed at capturing the execution logic of legal contracts. Ergo is intended to be accessible to Lawyers who create the corresponding prose for computable legal contracts. It is important that a developer and a lawyer can together agree that clauses in a computable legal contract have the same semantics as the equivalent Ergo code. However, as a programming language, the Ergo syntax should also respect programming conventionsHere are some thoughts and notes on requirements and on the
initial design.

## What is Ergo?

Ergo is a domain specific language designed to capture the execution
logic of *legal* contracts. Among some of the goals for the language
are:
- to have contracts and clauses as first-class elements of the language
- to help legal-tech developers quickly and safely write computable legal contracts
- to be modular, facilitating reuse of existing contract or clause logic
- to ensure safe execution: the language should prevent run-time errors and non-terminating logic
- to be blockchain neutral: the same contract logic can be executed either on and off chain on a variety of distributed ledger technologies
- to be formally specified: the meaning of contracts should be well defined so it can be verified, and preserved during execution
- to be consistent with the [Accord Protocol Template Specification](https://docs.google.com/document/d/1UacA_r2KGcBA2D4voDgGE8jqid-Uh4Dt09AE-shBKR0)

## Design choices

To achieve those goals the design of Ergo is based on the following
principles:

- Ergo contracts have a class-like structure with clauses akin to methods
- Ergo can handle types (concepts, transations, etc) defined with the [Hyperledger Composer Modeling Language](https://hyperledger.github.io/composer/latest/reference/cto_language) (so called CTO models), as mandated by the Accord Prototype Template Specification
- Ergo borrows from strongly-typed functional programming languages: clauses have a well-defined type signature (input and output), they are functions without side effects
- The compiler guarantees error-free execution for well-typed Ergo programs
- Clauses and functions are written in an expression language with limited expressiveness (it allows conditional and bounded iteration)
- Most of the compiler is written in Coq as a stepping stone for formal specification and verification

## Status

- The current implementation only supports the JavaScript backend for Cicero (and Hyperledger)
- CTO models are imported, but not used for type checking yet (but stay tuned!)

