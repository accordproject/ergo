---
id: ergo-expressions
title: Expressions
---

Computation in Ergo is written using expressions. Here are the
different kinds of expressions Ergo supports.

## Literal values

```
    "John Smith" // a string literal
    1            // an integer literal
    3.5e-10      // a floating point literal
```

## Operators

```
    1+2*3                // Arithmetic operators
    1 <= 3               // Comparison operators
    1 == 2
    2 > 1
    true or false        // Boolean operators
    true and false
    "Hello" ++ " World!" // String concatenation
```

## Local variable declarations

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
    define variable x : Double = 3.1416     // declares and initialize a double variable
    sqrt(x)                                 // rest of the expression
```

## Conditional expressions

See also the [Conditional Expression Reference](ergo-conditional-expressions.md)  

```
    if x < 0   // Condition
    then -x+1  // Expression if condition is true
    else x+1   // Expression if condition is false
```

## Match expressions

Match expressions allow to check an expression against multiple possible
values:

```
    match fruitcode
      with 1 then "Apple"
      with 2 then "Apricot"
      else "Strange Fruit"
```

## Foreach expressions

Foreach expressions allow to apply an expression of every element in
an input array of values and returns a new array:

```
foreach x in [1,-2,3] return x+1
```

Foreach expressions can have an optional condition of the values being
iterated over:

```
    foreach x in [1,-2,3] where x > 0 return x+1
```

## Object Creation

Creating objects (such as concepts or events) can be done using
``new`` with the name of the concept and the values for each fields:

```
    new Person{
      name: "John Smith",
      age: 32
    }
```

