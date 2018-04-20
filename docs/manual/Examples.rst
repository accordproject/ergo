Examples
========

Hello World
-----------

Ergo files are packages and can contain contracts. The following is a
simple “Hello World!” contract:

::

    package org.accordproject.helloworld

    contract HelloWorld over TemplateModel {
       // Simple Clause
       clause helloworld(request Request) : Response {
           new Response{ output: "Hello " ++ contract.name ++ " " ++ request.input }
      }
    }

It declares that the file belongs to the
``org.accordproject.helloworld`` package and contains a single
``HelloWorld`` contract with one ``helloworld`` clause.

It also declares that the contract ``HelloWorld`` is parameterized over
a given ``TemplateModel``.

The ``TemplateModel`` as well as the ``Request`` and ``Response`` are
types which can be specified using the Hyperledger CTO format.

The clause takes a ``Request`` as input and returns a ``Response``.

The code for the clause just constructs a new ``Response`` with a
property ``output`` which is a string containing the property ``name``
of from the contract (``contract``) and the property ``input`` from the
request (``request``).

