---
id: ergo-match-expressions
title: Match Expressions
---

Match expressions allow us to check an expression against multiple
possible values or patterns. If a match is found, then Ergo will
evaluate the corresponding expression.

> Match expressions are similar to `switch` statements in other
> programming languages

Example
-------

``` {.sourceCode .js}
match request.status
  with "CREATED" then
    new PayOut{ amount : contract.deliveryPrice }
  with "ARRIVED" then
    new PayOut{ amount : contract.deliveryPrice - shockPenalty }
  else
    new PayOut{ amount : 0 }
```

Legal Prose
-----------

> Example needed.

Syntax
------

``` {.sourceCode .js}
match expression1        
  with expression2 then       // Repeat this line
    expression3               //    and this line
  else
    expression4         
```

Usage
-----

### Example 1

You can use a match expression to look for patterns based on the type of
an expression.

``` {.sourceCode .js}
match response
    with let b1 : BuyerMayTerminateResponse then
        // Do something with b1
    with let b2 : BuyerMayNotTerminateResponse then
        // Do something with b2
    else
        // Do a default action
```

### Example 2

Often a match expression is a more consise way to represent a
conditional expression with a repeating, regular condition. For example:

```
    if x = 1 then
      ...
    else if x = 2 then
      ...
    else if x = 3 then
      ...
    else if x = 4 then
      ...
    else
      ...
```

This is equivalent to the match expression:

```
    match x
      with 1 then
        ...
      with 2 then
        ...
      with 3 then
        ...
      with 4 then
        ...
      else
        ...
```