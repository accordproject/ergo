# Jura Language

This contains a few notes on the Jura language.

## General

Jura files have the `.jura` extension.

## Packages

Jura files are packages and contain contracts. The following is a
simple "Hello World!" contract:

```
package org.accordproject.helloworld

contract HelloWorld over TemplateModel {
   // Simple Clause
   clause helloworld(request Request) Response {
       new Response{ output: "Hello " + this.name + " " + request.input }
  }
}
```

It declares the package the file belongs to and a single `HelloWorld`
contract with a single `helloworld` clause.

The contract `HelloWorld` is parameterized over a given
`TemplateModel`.

The clause takes a `Request` as input and returns a `Response`.

The code for the clause just constructs a new `Response` with a
property `output` which is a string containing the property `name` of
from the contract (`this`) and the property `input` from the request.

