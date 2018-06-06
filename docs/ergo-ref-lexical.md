---
id: ergo-ref-lexical
title: Lexical conventions
---

## File Extension

Ergo files have the ``.ergo`` extension.

## Blanks

Blank characters (such as space, tabulation, carriage return) are
ignored but they are used to separate identifiers.

## Comments

Comments come in two forms. Single line comments are introduced by the
two characters `//` and are terminated by the end of the current
line. Multi-line comments start with the two characters `/*` and are
terminated by the two characters `*/`. Multi-line comments can be
nested.

Here are examples of comments:

```
    // This is a single line comment
    /* This comment spans multiple lines
       and it can also be /* nested */ */
```

## Reserved words

The following are reserved as keywords in Ergo. They cannot be used as identifiers.

```markdown
namespace, import, define, function, concept, transaction, enum,
extends, contract, over, clause, throws, state, enforce, if,
then, else, let, foreach, return, in, where, return, throw, new,
contract, clause, variable, as, match, set, emit, with, or, and,
true, false, nil
```

