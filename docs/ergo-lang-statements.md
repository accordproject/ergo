---
id: ergo-lang-statements
title: Statements
---

Clauses body are statements. They may return a response or an error. They may also change the contract state or emit events.

## Return statement

Returning a response from a clause can be done by using a return statement:

```
     return 1                           // Return the integer one
     return new Payout{ amount: 39.99 } // Return a new Payout object
     return                             // Return nothing
```

## Throw statement

Returning an error can be done by using a throw statement:

```
     throw "Something went wrong"          // Return an error as a string
     return new Error{ message: "oops!" }  // Return an error as an object
```

## Enforce statement

Before a contract is enforceable some preconditions must be satisfied:
- Competent parties who have the legal capacity to contract
- Lawful subject matter
- Mutuality of obligation
- Consideration

The constructs below will be used to determine if the preconditions have been met and what actions to take if they are not

```
Example Prose
    Do the parties have adequate funds to execute this contract?  
```

One can check preconditions in a clause using enforce statements, as
follows:

```
    enforce x >= 0                     // Condition
    else throw "Something went wrong"; // Statement if condition is false
    return x+1                         // Statement if condition is true
```

The else part of the statement can be ommitted in which case Ergo
returns an error by default.

```
    enforce x >= 0;           // Condition
    return x+1                // Statement if condition is true
```

