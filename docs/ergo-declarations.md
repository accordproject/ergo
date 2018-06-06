---
id: ergo-declarations
title: Declarations
---

# Global Variables Declarations

It is possible to declare global variables and functions in Ergo:

```
    define variable pi = 3.1416
    define function area(radius Double) : Double {
      pi * r * r
    }
    area(1.5)
```

# Contracts Declarations

You can declare a contract over a template model as follows:

```
    contract ContractName over TemplateModel {
      clause C1(request : ReqType1) : RespType1 {
        // Expression
      }

      clause C2(request : ReqType2) : RespType2 {
        // Expression
      }
    }
```

When inside a contract, the `contract` variable contains the instance
of the Template for the current contract.

When inside a clause, the `clause` variable contains the part of the
Template instance specific to that clause.
