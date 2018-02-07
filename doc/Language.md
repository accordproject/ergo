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
