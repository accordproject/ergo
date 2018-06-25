---
id: ergo-lang-types
title: Types
---

In Ergo, types are based on the Hyperledger Composer Modeling Language (referred to in this document as CTO models). https://hyperledger.github.io/composer/latest/reference/cto_language.htm. One can either import an existing CTO file, or declare types within Ergo itself. One can either import an existing CTO file, or declare types within Ergo
itself.

As we have seen in previous examples, one can refer to types in variable
declarations or in functions/clauses signatures.

## Atomic types

Atomic data types are data elements that represent the lowest level of detail. Atomic data types have a common set of properties which include class name, total data size, byte order referring to how the bits are arranged as they reside in memory, precision which refers to the significant part of a data, offset or the location of the significant data within the entire data itself and padding which identifies that data which is not significant.

Here are the Ergo base types:

```
    Boolean
    String
    Double
    Long
    Integer
    DateTime
```

## Records

A Record (also called a structure, struct, or compound data) is a basic data structure. Records in a database or spreadsheet are usually called "rows". A record is a collection of fields, possibly of different data types, typically in fixed number and sequence.

```
    { name: String, age: Long } // Record with two attributes:
                                // a name and an age
```

## Arrays

Arrays can hold many values under a single name, and you can access the values by referring to an index number.
Here are array types:

```
    String[]                      // Array of String values
    Product[]                     // Array of Product (a declared type)
    { name: String, age: Long }[] // Array of records
```

## Enums

Enums are used to represent a fixed number of possible values. Here is how to declare an enumeration:

```
    define enum ProductType {
     DAIRY,
     BEEF,
     VEGETABLES
    }
```

## Classes

Here is how to declare CTO classes (either concepts or transactions in
CTO terminology):

```
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
```

