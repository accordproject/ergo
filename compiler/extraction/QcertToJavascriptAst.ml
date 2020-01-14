open ForeignToJavaScriptAst
open JsSyntax
open QcertEJson

(** val enhanced_ejson_to_ajavascript_expr : enhanced_ejson -> expr **)

let enhanced_ejson_to_ajavascript_expr _ =
  Coq_expr_literal Coq_literal_null

(** val enhanced_foreign_ejson_to_ajavascript :
    enhanced_ejson foreign_ejson_to_ajavascript **)

let enhanced_foreign_ejson_to_ajavascript =
  enhanced_ejson_to_ajavascript_expr
