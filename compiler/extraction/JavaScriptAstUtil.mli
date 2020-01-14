open JsSyntax

val array_push : expr -> expr -> expr

val array_get : expr -> expr -> expr

val object_hasOwnProperty : expr -> expr -> expr

val call_js_function : char list -> expr list -> expr

val call_runtime : char list -> expr list -> expr
