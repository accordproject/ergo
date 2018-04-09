# Conditional Expressions

Conditional expressions (also known as `if` statements) allow us to conditionally execute Ergo code depending on the value of a test condition. If the test condition evaluates to `true` then the code on the `then` branch is evaluated. Otherwise, when the test condition evaluates to `false` then the `else` branch is evaluated.

## Example

```js
if delayInDays > 15 then
  new BuyerMayTerminateResponse{};
else 
  new BuyerMayNotTerminateResponse{}
```

## Legal Prose
For example, this corresponds to a conditional logic statement in legal prose.

```
If the delay is more than 15 days, the Buyer is entitled to terminate this Contract.
```

## Syntax
```
if expression1 then     // Condition
  expression2           // Expression if condition is true
else
  expression3           // Expression if condition is false
```

Where `expression1` is an Ergo expression that evaluates to a [Boolean value](Types.md#Boolean) (i.e. `true` or `false`), and `expression2` and `expression3` are Ergo expressions.

> Note that as with all Ergo expressions, new lines and indentation don't change the meaning of your code. However it is good practice to standardise the way that you using whitespace in your code to make it easier to read.

## Usage

Conditional expressions can be chained to build more complex expressions.
```js
if request.netAnnualChargeVolume < contract.firstVolume then
  return new VolumeDiscountResponse{ discountRate: contract.firstRate }
else if request.netAnnualChargeVolume < contract.secondVolume then 
  return new VolumeDiscountResponse{ discountRate: contract.secondRate }
else 
  return new VolumeDiscountResponse{ discountRate: contract.thirdRate }
```

Conditional expressions can also be used in [variable declarations](VariableDeclarations.md).

```js
define variable price = 42;
define variable message =  if price > 100 then "High price" else "Low Price";
message;
```

The value of message after running this code will be `"Low Price"`.

## Related

* [Match expression](MatchExpressions.md) - where you have many alternative conditions that check the same variable.
* [Boolean type](Types.md#Boolean) - a true or false value
