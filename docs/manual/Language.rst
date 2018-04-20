This contains a few notes on the Ergo language.

General
-------

Ergo files have the ``.ergo`` extension.

Comments
--------

Comments in Ergo are written in a commonly used style:

::

    // This is a single line comment
    /* This comment spans multiple lines
       and it can also be /* nested */ */

Expressions
-----------

The logic for individual clauses in Ergo is written using expressions.
Here are the expressions Ergo supports.

Literal values
~~~~~~~~~~~~~~

::

    "John Smith" // a string literal
    1            // an integer literal
    3.5e-10      // a floating point literal

Operators
~~~~~~~~~

::

    1+2*3                // Arithmetic operators
    1 <= 3               // Comparison operators
    1 == 2
    2 > 1
    true or false        // Boolean operators
    true and false
    "Hello" ++ " World!" // String concatenation

Local variable declarations
~~~~~~~~~~~~~~~~~~~~~~~~~~~

::

    define variable x = 1; // declares and initialize a variable
    x+2                    // rest of the expression, with variable x in scope

Local variables can also be declared with the shorter ``let`` form:

::

    let x = 1;             // declares and initialize a variable
    x+2                    // rest of the expression, with variable x in scope

Local variables can also be declared with a type:

::

    define variable name : String = "John"; // declares and initialize a string variable
    name ++ " Smith"                        // rest of the expression
    let x : Double = 3.1416;                // declares and initialize a double variable
    sqrt(x)                                 // rest of the expression

Conditionals
~~~~~~~~~~~~

:doc:`Full Documentation <reference/ConditionalExpressions>`
::

    if x < 0   // Condition
    then -x+1  // Expression if condition is true
    else x+1   // Expression if condition is false


Enforce expressions
~~~~~~~~~~~~~~~~~~~

One can check preconditions in a clause using enforce expressions, as
follows:

::

    enforce x >= 0               // Condition
    else "Something went wrong"; // Expression if condition is false
    x+1                          // Expression if condition is true

The else part of the expression can be ommitted in which case Ergo
returns an error by default.

::

    enforce x >= 0;           // Condition
    x+1                       // Expression if condition is true

Match expressions
~~~~~~~~~~~~~~~~~

Match expressions allow to check an expression against multiple possible
values:

::

    match fruitcode
      with 1 then "Apple"
      with 2 then "Apricot"
      else "Strange Fruit"

For expressions
~~~~~~~~~~~~~~~

For expressions allow to apply an expression of every element in an
input array of values:

::

    for x in [1,-2,3] { x+1 }

For expressions can have an optional condition of the values being
iterated over:

::

    for x in [1,-2,3] where x > 0 { x+1 }

Creating objects
~~~~~~~~~~~~~~~~

Creating objects (such as CTO concepts, transactions, or Ergo errors)
can be done using ``new`` with the name of the concept and the values
for each fields:

::

    new Person{
      name: "John Smith",
      age: 32
    }

Functions
---------

It is possible to declare functions in Ergo:

::

    define variable pi = 3.1416
    define function area(radius Double) : Double {
      pi * r * r
    }
    area(1.5)

Types
-----

One either import an existing CTO file, or declare types within Ergo
itself.

As we have seen in previous examples, one can refer to types in variable
declarations or in functions/clauses signatures.

Here are atomic types:

::

    Boolean                   // Atomic types
    String
    Double
    Long
    Integer
    DateTime

Here is a record (sometimes called a struct in other languages):

::

    { name: String, age: Long } // Record with two attributes:
                                // a name and an age

Here are array types:

::

    String[]                      // Array of String values
    Product[]                     // Array of Product (a declared type)
    { name: String, age: Long }[] // Array of records

Here is how to declare CTO classes (either concepts or transactions in
CTO terminology):

::

    define concept Product {
       id : String
    }
    define concept Car extends Product {
       range : String
    }
    define transaction Response {
       rate : Double,
       penalty : Double
    }
    define enum ProductType {
     DAIRY,
     BEEF,
     VEGETABLES
    }

Contracts *NEW*
---------------

You can declare a contract over a template model as follows:

::

    contract ContractName over TemplateModel {
      clause C1(request ReqType1) : RespType1 {
        // Expression
      }

      clause C2(request ReqType2) : RespType2 {
        // Expression
      }
    }

When inside a contract, the ``contract`` variable contains the instance
of the Template for the current contract.

When inside a clause, the ``clause`` variable contains the part of the
Template instance specific to that clause.
