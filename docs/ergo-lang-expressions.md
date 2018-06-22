## Expressions
The logic for individual clauses in Ergo is written using statements and expressions. Here below are the currently  supported statements and expressions.
Literal values
A literal is a notation for representing a fixed value in Ergo. Most programming languages have notations for atomic values such as integers, floating-point numbers, strings, booleans and characters;  as well as notations for elements of enumerated types and compound values such as arrays, records, and objects.
    "John Smith" // a string literal
    1            // an integer literal
    3.5e-10      // a floating point literal
## Operators
Ergo supports a set of operators: constructs which behave generally like functions, but which differ syntactically or semantically from usual functions. Ergo operators include arithmetic (addition with +), comparison (with >), logical operations (such as and or &&) and concatenation operators (like ++).
    1+2*3                // Arithmetic operators
    1 <= 3               // Comparison operators
    1 == 2
    2 > 1
    true or false        // Boolean operators
    true and false
    "Hello" ++ " World!" // String concatenation
## Local variable declarations
There are two levels of visibility, local variables are contrasted with global variables. A local variable is a variable that is given local scope. Local variable references in the function or block in which it is declared override the same variable name in the larger scope. 
    define variable x = 1; // declares and initialize a variable
    x+2                    // rest of the expression, with variable x in scope
Local variables can also be declared with the shorter let form:
    let x = 1;             // declares and initialize a variable
    x+2                    // rest of the expression, with variable x in scope
Local variables can also be declared with a type:
    define variable name : String = "John"; // declares and initialize a string variable
    name ++ " Smith"                        // rest of the expression
    define variable x : Double = 3.1416     // declares and initialize a double variable
    sqrt(x)                                 // rest of the expression
## The If statement and Conditionals
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
## Enforce expressions
Before a contract is enforceable some preconditions such as the following must be satisfied:
•	Competent parties who have the legal capacity to contract
•	Lawful subject matter
•	Mutuality of obligation
•	Consideration
The constructs below will be used to determine if the preconditions have been met and what actions to take if they are not
Example Prose
    Do the parties have adequate funds to execute this contract?  
One can check preconditions in a clause using enforce expressions, as follows:
    enforce x >= 0               // Condition
    else "Something went wrong"; // Expression if condition is false
    x+1                          // Expression if condition is true
The else part of the expression can be omitted in which case Ergo returns an error by default.
    enforce x >= 0;           // Condition
    x+1                       // Expression if condition is true
## Match expressions
The Match compares a given value with specified constants and take action according to the first constant to match. There is a provision for a default action ('else') to be taken if no match succeeds
    match fruitcode
      with 1 then "Apple"
      with 2 then "Apricot"
      else "Strange Fruit"


Match expressions allow us to check an expression against multiple possible values or patterns. If a match is found, then Ergo will evaluate the corresponding expression.
Match expressions are similar to switch statements in other programming languages
Example
match request.status
  with "CREATED" then
    new PayOut{ amount : contract.deliveryPrice }
  with "ARRIVED" then
    new PayOut{ amount : contract.deliveryPrice - shockPenalty }
  else
    new PayOut{ amount : 0 }
Legal Prose
Example needed.
Syntax
match expression1        
  with expression2 then       // Repeat this line
    expression3               //    and this line
  else
    expression4         
Usage
Example 1
You can use a match expression to look for patterns based on the type of an expression.
match response
    with let b1 : BuyerMayTerminateResponse then
        // Do something with b1
    with let b2 : BuyerMayNotTerminateResponse then
        // Do something with b2
    else
        // Do a default action
Example 2
Often a match expression is a more consise way to represent a conditional expression with a repeating, regular condition. For example:
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
This is equivalent to the match expression:
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

## For expressions
A foreach loop is a control flow statement/expression for specifying iteration, which allows code to be executed repeatedly. A foreach has two parts: a header specifying the iteration, and a body which is executed once per iteration. The header declares an explicit loop array, which allows the body to know which iteration is being executed. Foreach is used when the number of iterations is known before entering the loop. Foreach expressions allow to apply an expression of every element in an input array of values and returns a new array:
foreach x in [1,-2,3] return x+1
For expressions can have an optional condition of the values being iterated over:
    foreach x in [1,-2,3] where x > 0 return x+1
## Creating objects
An object can be a variable, a data structure, a function, or a method, and as such, is a location in memory having a value and referenced by an identifier. In the class-based object-oriented programming "object" refers to a particular instance of a class where the object can be a combination of variables, functions, and data structures. Creating objects (such as CTO concepts, transactions, or Ergo errors) can be done using new with the name of the concept and the values for each fields:
    new Person{
      name: "John Smith",
      age: 32
    }
