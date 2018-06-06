---
id: ergo-language
title: Ergo Language
---

## Enforce expressions

Before  a contract is enforceable some preconditions must be satisfied:
- Competent parties who have the legal capacity to contract
- Lawful subject matter
- Mutuality of obligation
- Consideration

The constructs below will be used to determine if the preconditions have been met and what actions to take if they are not

```
Example Prose
    Do the parties have adequate funds to execute this contract?  
```

One can check preconditions in a clause using enforce expressions, as
follows:

```
    enforce x >= 0               // Condition
    else "Something went wrong"; // Expression if condition is false
    x+1                          // Expression if condition is true
```

The else part of the expression can be ommitted in which case Ergo
returns an error by default.

```
    enforce x >= 0;           // Condition
    x+1                       // Expression if condition is true
```

# Functions

It is possible to declare global variables and functions in Ergo:

```
    define variable pi = 3.1416
    define function area(radius Double) : Double {
      pi * r * r
    }
    area(1.5)
```

# Contracts *NEW*

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
