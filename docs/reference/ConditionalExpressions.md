# Conditional Expressions

Conditional expressions (also known as `if` statements) allow us to conditionally execute Ergo code depending on the value of a test condition. If the test condition evaluates to `true` then the code on the `then` branch is evaluated. Otherwise, when the test condition evaluates to `false` then the `else` branch is evaluated.

### Syntax
```js
if expression   // Condition
then expression  // Expression if condition is true
else expression   // Expression if condition is false
```

### Legal Prose
For example, this corresponds to a conditional logic statement in legal prose.

```
If the delay is more than 15 days, the Buyer is entitled to terminate this Contract.
```

### Example

```js
if delayInDays > 15 then
    new BuyerMayTerminateResponse{};
else 
    new BuyerMayNotTerminateResponse{}
```



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

* [Match expression](#) - where you have many alternative conditions that check the same variable.
* [Boolean type](#) - a true or false value
