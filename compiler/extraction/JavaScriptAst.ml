open JsSyntax

type topdecl =
| Coq_strictmode
| Coq_comment of char list
| Coq_elementdecl of element
| Coq_classdecl of char list * funcdecl list
| Coq_constdecl of char list * expr

type js_ast = topdecl list
