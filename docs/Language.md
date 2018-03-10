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
   clause helloworld(request Request) : Response {
       new Response{ output: "Hello " ++ this.name ++ " " ++ request.input }
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

### Literal values:

```
"John Smith" // a string literal
1            // an integer literal
3.5e-10      // a floating point literal
```

### Operators:
```
1+2*3                // Arithmetic operators
1 <= 3               // Comparison operators
1 == 2
2 > 1
true or false        // Boolean operators
true and false
"Hello" ++ " World!" // String concatenation
```

### Local variable declarations:
```
define variable x = 1; // declares and initialize a variable
x+2                    // rest of the expression, with variable x in scope
```
Local variables can also be declared with the shorter `let` form:
```
let x = 1;             // declares and initialize a variable
x+2                    // rest of the expression, with variable x in scope
```
Local variables can also be declared with a type:
```
define variable name : String = "John"; // declares and initialize a string variable
name ++ " Smith"                        // rest of the expression
let x : Double = 3.1416;                // declares and initialize a double variable
sqrt(x)                                 // rest of the expression
```

### Conditionals:
```
if x < 0   // Condition
then -x+1  // Expression if condition is true
else x+1   // Expression if condition is false
```

### Ensure expressions
One can check preconditions in a clause using ensure expressions, as follows:
```
ensure x >= 0                // Condition
else "Something went wrong"; // Expression if condition is false
x+1                          // Expression if condition is true
```
The else part of the expression can be ommitted in which case Jura returns an error by default.
```
ensure x >= 0;            // Condition
x+1                       // Expression if condition is true
```

### Creating objects

Creating objects (such as CTO concepts, transactions, or Jura errors)
can be done using `new` with the name of the concept and the values
for each fields:
```
new Person{
  name: "John Smith",
  age: 32
}
```

### Match expressions

Match expressions allow to check an expression against multiple
possible values:
```
match fruitcode
  with 1 then "Apple"
  with 2 then "Apricot"
  else "Strange Fruit"
```

For expressions allow to apply an expression of every element in an input array of values:
```
for x in [1,-2,3] { x+1 }
```

For expressions can have an optional condition of the values being iterated over:
```
for x in [1,-2,3] where x > 0 { x+1 }
```

## Functions

It is possible to declare functions in Jura:
```
define variable pi = 3.1416
define function area(radius Double) : Double {
  pi * r * r
}
area(1.5)
```
