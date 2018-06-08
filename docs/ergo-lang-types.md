---
id: ergo-lang-types
title: Types
---

In Ergo, types are based on the Hyperledger Composer Modeling Language (referred to in this document as CTO models). https://hyperledger.github.io/composer/latest/reference/cto_language.htm. One can either import an existing CTO file, or declare types within Ergo itself. One can either import an existing CTO file, or declare types within Ergo
itself.

As we have seen in previous examples, one can refer to types in variable
declarations or in functions/clauses signatures.

## Atomic types

Here are the base types:

```
    Boolean
    String
    Double
    Long
    Integer
    DateTime
```

## Records

Here is a record (sometimes called a struct in other languages):

```
    { name: String, age: Long } // Record with two attributes:
                                // a name and an age
```

## Arrays

Here are array types:

```
    String[]                      // Array of String values
    Product[]                     // Array of Product (a declared type)
    { name: String, age: Long }[] // Array of records
```

## Enums

Here is how to declare an enumeration:

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

