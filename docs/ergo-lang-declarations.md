---
id: ergo-lang-declarations
title: Declarations
---

## Global Variables Declarations

It is possible to declare global variables and functions in Ergo:

```
    define variable pi = 3.1416
    define function area(radius Double) : Double {
      pi * r * r
    }
    area(1.5)
```

## Contracts Declarations
In the legal sense the elements of a contract are as follows. The requisite elements that must be established to demonstrate the formation of a legally binding contract are (1) offer; (2) acceptance; (3) consideration; (4) mutuality of obligation; (5) competency and capacity; and, in certain circumstances, (6) a written instrument. 

Ergo will be able to enforce the Accord template resultant code dealing with consideration, mutuality of obligation, competency and capacity through statements we will describe in this document. 

The best part is that the Ergo contract is an immutable written instrument which will obviate a good deal of the issues and conflicts which emerge from existing contracts in use today.  In Ergo, a contract represents an agreement between parties creating mutual and enforceable obligations. In Ergo , a contract is a specific  class of code that uses conditionals and functions to describe execution by the parties with their obligations. Contracts accept input consisting of the parties and the terms as data which matches the parameters defined in the contract. The contract then uses functions to process it, and "return" a result, i.e. how the contract execution proceeds. Once a domain specific contract is written, it can be used over and over and over again. Contracts can be "called" from the inside of other contracts.

Contracts when created instantiate a particular domain agreement. They combine functions and clauses to execute a specific agreement and to allow its execution using a single line of code. This also bodes well for a legal DSL as many contracts are “boilerplate” and as such are reusable in their specific legal domain, e.g., sale of goods


You can declare a contract over a template model as follows:

```
    contract ContractName over TemplateModel {
      clause C1(request : ReqType1) : RespType1 {
        // Expression
      }

      clause C2(request : ReqType2) : RespType2 {
        // Expression
      }
    }
```

When inside a contract, the `contract` variable contains the instance
of the Template for the current contract.

When inside a clause, the `clause` variable contains the part of the
Template instance specific to that clause.
