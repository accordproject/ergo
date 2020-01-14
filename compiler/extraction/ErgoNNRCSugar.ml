open BinaryOperators
open Data
open Datatypes
open ErgoNNRC
open Fresh
open List0
open QcertData
open UnaryOperators
open CNNRC
open CNNRCVars

(** val fresh_in_match :
    ('a1 * ergo_nnrc_expr) list -> ergo_nnrc_expr -> char list **)

let fresh_in_match eccases ecdefault =
  fresh_var ('$'::('m'::('a'::('t'::('c'::('h'::[]))))))
    (app
      (concat
        (map (fun eccase ->
          nnrc_free_vars enhanced_foreign_runtime (snd eccase)) eccases))
      (nnrc_free_vars enhanced_foreign_runtime ecdefault))

(** val fresh_in_case : ergo_nnrc_expr -> ergo_nnrc_expr -> char list **)

let fresh_in_case pattern_expr else_expr =
  fresh_var ('$'::('c'::('a'::('s'::('e'::[])))))
    (app (nnrc_free_vars enhanced_foreign_runtime pattern_expr)
      (nnrc_free_vars enhanced_foreign_runtime else_expr))

(** val new_array : ergo_nnrc_expr list -> ergo_nnrc_expr **)

let new_array = function
| [] -> NNRCConst (Coq_dcoll [])
| e1 :: erest ->
  fold_left (fun acc e -> NNRCBinop (OpBagUnion, acc, (NNRCUnop (OpBag, e))))
    erest (NNRCUnop (OpBag, e1))

(** val new_expr : char list -> ergo_nnrc_expr -> ergo_nnrc_expr **)

let new_expr brand struct_expr =
  NNRCUnop ((OpBrand (brand :: [])), struct_expr)
