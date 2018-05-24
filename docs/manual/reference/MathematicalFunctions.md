Mathematical Functions
=======================

These mathematical aggregate functions allow your logic to calculate the average, sum, max, min of a list of values.

Example
-------

``` {.sourceCode .js}
define variable values = [0.2, 0.3, 1.2];
define variable x = max(values);  // 1.2
define variable y = min(values);  // 0.2
define variable s = sum(values);  // 1.7
define variable a = average(values);  // 0.5666666666666667 
```

Syntax
------

    max(array1) 
  
Where `array1` is an expression that evaluates to 

> Note that as with all Ergo expressions, new lines and indentation
> don't change the meaning of your code. However it is good practice to
> standardise the way that you using whitespace in your code to make it
> easier to read.

Usage
-----

Conditional expressions can be chained to build more complex
expressions.

``` {.sourceCode .js}
if request.netAnnualChargeVolume < contract.firstVolume then
  return new VolumeDiscountResponse{ discountRate: contract.firstRate }
else if request.netAnnualChargeVolume < contract.secondVolume then 
  return new VolumeDiscountResponse{ discountRate: contract.secondRate }
else 
  return new VolumeDiscountResponse{ discountRate: contract.thirdRate }
```

Conditional expressions can also be used in [variable
declarations \<VariableDeclarations\>]{role="doc"}.

``` {.sourceCode .js}
define variable price = 42;
define variable message =  if price > 100 then "High price" else "Low Price";
message;
```

The value of message after running this code will be `"Low Price"`.

Related
-------

-   [Match expression](MatchExpressions.md) - where many
    alternative conditions check the same variable
