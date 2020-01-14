open ForeignEJson
open JsSyntax

type 'foreign_ejson_model foreign_ejson_to_ajavascript =
  'foreign_ejson_model -> expr
  (* singleton inductive, whose constructor was mk_foreign_ejson_to_ajavascript *)

val foreign_ejson_to_ajavascript_expr :
  'a1 foreign_ejson -> 'a1 foreign_ejson_to_ajavascript -> 'a1 -> expr
