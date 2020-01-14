open Ast
open Datatypes
open Ergo
open ErgoType
open Names
open Provenance
open QLib
open TBrandModel

type tlaergo_pattern = (provenance * qcert_type, absolute_name) ergo_pattern

type tlaergo_expr =
  (provenance * qcert_type, provenance, absolute_name) ergo_expr

type ergoct_expr = tlaergo_expr

(** val exprct_type_annot : brand_model -> ergoct_expr -> qcert_type **)

let exprct_type_annot _ e =
  snd (expr_annot e)

type sigct = { sigct_params : (char list * qcert_type) list;
               sigct_output : qcert_type }

type ergoct_function = { functionct_annot : provenance;
                         functionct_sig : sigct;
                         functionct_body : ergoct_expr option }

type ergoct_contract = { contractct_annot : provenance;
                         contractct_clauses : (local_name * ergoct_function)
                                              list }

type ergoct_declaration =
| DCTExpr of (provenance * qcert_type) * ergoct_expr
| DCTConstant of (provenance * qcert_type) * absolute_name
   * laergo_type option * ergoct_expr
| DCTFunc of provenance * absolute_name * ergoct_function
| DCTContract of provenance * absolute_name * ergoct_contract

(** val ergoct_declaration_type :
    brand_model -> ergoct_declaration -> qcert_type option **)

let ergoct_declaration_type _ = function
| DCTExpr (p, _) -> let (_, t) = p in Some t
| DCTConstant (p, _, _, _) -> let (_, t) = p in Some t
| _ -> None

type ergoct_module = { modulect_annot : provenance;
                       modulect_namespace : char list;
                       modulect_declarations : ergoct_declaration list }
