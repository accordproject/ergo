# Jura Language

This contains a few notes on the Jura language.

## General

Jura files have the `.jura` extension.

## Hello World

Jura files are packages and can contain contracts. The following is a
simple "Hello World!" contract:
```
package org.accordproject.helloworld

contract HelloWorld over TemplateModel {
   // Simple Clause
   clause helloworld(request Request) Response {
       new Response{ output: "Hello " + this.name + " " + request.input }
  }
}
```

It declares that the file belongs to the
`org.accordproject.helloworld` package and contains a single
`HelloWorld` contract with one `helloworld` clause.

It also declares that the contract `HelloWorld` is parameterized over
a given `TemplateModel`.

The `TemplateModel` as well as the `Request` and `Response` are types
which can be specified using the Hyperledger CTO format.

The clause takes a `Request` as input and returns a `Response`.

The code for the clause just constructs a new `Response` with a
property `output` which is a string containing the property `name` of
from the contract (`this`) and the property `input` from the request
(`request`).

## Comments

Comments in Jura are written in a commonly used style:

```
// This is a single line comment
/* This comment spans multiple lines
   and it can also be /* nested */ */
```

## Expressions

The logic for individual clauses in Jura is written using
expressions. Here are the expressions Jura supports.

Literal values:

```
"John Smith" // a string literal
1            // an integer literal
3.5e-10      // a floating point literal
```

Let bindings:
```
let x = 1;   // declares and initialize a variable
x+2          // rest of the expression, with variable x in scope
```

Conditionals:
```
if x < 0 {   // Condition
  -x+1       // Expression evaluated if the condition is true
} else {
  x+1        // Expression evaluated if the condition is false
}
```

Guards:
```
guard x >= 0 else {       // Condition
  "Something went wrong"  // Expression evaluated if condition is false
}
```
Guards can be useful to check preconditions in a clause

Creating objects (such as CTO concepts, transactions, or Jura errors):
```
new Person{
  name: "John Smith",
  age: 32
}
```
