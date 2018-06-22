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
## Clauses
In Ergo, a logical clause like the example clause noted below is represented as a “function” (akin to a “method” in languages like Java) that resides within its parent contract (akin to a “class” in a language like Java). Functions are "self contained" modules of code that accomplish a specific task. Functions usually "take in" data, process it, and "return" a result. Once a function is written, it is reusable , i.e., it can be used over and over and over again. Functions can be "called" from within other functions or from a clause. Functions have to be declared before they can be used.
So functions "encapsulate" a task. They combine statements and expressions carried out as instructions which accomplish a specific task to allow their execution using a single line of code. Most programming languages provide libraries of built in functions (i.e., commonly used tasks like computing the square root of a number). Functions accelerate development and facilitate the reuse of code which performs common tasks. This bodes well for a legal DSL as many clauses known as “boilerplate” are in effect standards which are reused in many different agreement and contract types. In general, we don't care how a function does what it does, only that it "does it" making it a reliable language construct. When inside a clause, the clause variable contains the part of the Template instance specific to that clause. The interface of a Clause that contains the clause’s name, request type and return type collectively referred to as the ‘signature’ of the function.
Example Prose
Additionally the Equipment should have proper devices on it to record any shock during transportation as any instance of acceleration outside the bounds of -0.5g and 0.5g.
Each shock shall reduce the Contract Price by $5.00

Syntax 
```
    clause fragileGoods(request DeliveryUpdate) : ContractPrice {
  ... // An expression computing the result of the clause
}
```
...

When inside a contract, the `contract` variable contains the instance
of the Template for the current contract.

When inside a clause, the `clause` variable contains the part of the
Template instance specific to that clause.
