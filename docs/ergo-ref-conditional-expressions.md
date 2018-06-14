The If statement and Conditionals
Conditional statements, conditional expressions and conditional constructs are features of a programming language, which perform different computations or actions depending on whether a programmer-specified boolean condition evaluates to true or false.  Conditional expressions (also known as if statements) allow us to conditionally execute Ergo code depending on the value of a test condition. If the test condition evaluates to true then the code on the then branch is evaluated. Otherwise, when the test condition evaluates to false then the else branch is evaluated.
Example
if delayInDays > 15 then
  new BuyerMayTerminateResponse{};
else 
  new BuyerMayNotTerminateResponse{}
Legal Prose
For example, this corresponds to a conditional logic statement in legal prose.
If the delay is more than 15 days, the Buyer is entitled to terminate this Contract.
Syntax
if expression1 then     // Condition
  expression2           // Expression if condition is true
else
  expression3           // Expression if condition is false
Where expression1 is an Ergo expression that evaluates to a Boolean value (i.e. true or false), and expression2 and expression3 are Ergo expressions.
Note that as with all Ergo expressions, new lines and indentation don't change the meaning of your code. However, it is good practice to standardize the way that you use whitespace in your code to make it easier to read.
Usage
If statements can be chained , i.e., if then else if then else to build more compound conditionals.
if request.netAnnualChargeVolume < contract.firstVolume then
  return new VolumeDiscountResponse{ discountRate: contract.firstRate }
else if request.netAnnualChargeVolume < contract.secondVolume then 
  return new VolumeDiscountResponse{ discountRate: contract.secondRate }
else 
  return new VolumeDiscountResponse{ discountRate: contract.thirdRate }
Conditional expressions can also be used in variable declarations.
define variable price = 42;
define variable message =  if price > 100 then "High price" else "Low Price";
message;
The value of message after running this code will be "Low Price".
    if x < 0   // Condition
    then -x+1  // Expression if condition is true
    else x+1   // Expression if condition is false

Related
-------

-   [Match expression](ergo-match-expressions.md) - where many
    alternative conditions check the same variable
