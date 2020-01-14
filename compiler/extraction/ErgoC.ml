open Ergo
open ErgoType
open Names
open Provenance

type ergoc_expr = laergo_expr

type sigc = { sigc_params : (char list * laergo_type) list;
              sigc_output : laergo_type option }

type ergoc_function = { functionc_annot : provenance; functionc_sig : 
                        sigc; functionc_body : ergoc_expr option }

(** val bodyc_annot : ergoc_function -> provenance **)

let bodyc_annot f =
  match f.functionc_body with
  | Some e -> expr_annot e
  | None -> f.functionc_annot

type ergoc_contract = { contractc_annot : provenance;
                        contractc_template : laergo_type;
                        contractc_state : laergo_type option;
                        contractc_clauses : (local_name * ergoc_function) list }

type ergoc_declaration =
| DCExpr of provenance * ergoc_expr
| DCConstant of provenance * absolute_name * laergo_type option * ergoc_expr
| DCFunc of provenance * absolute_name * ergoc_function
| DCContract of provenance * absolute_name * ergoc_contract

type ergoc_module = { modulec_annot : provenance;
                      modulec_namespace : char list;
                      modulec_declarations : ergoc_declaration list }

(** val lookup_clausec_request_signatures :
    (local_name * ergoc_function) list -> (local_name * sigc) list **)

let rec lookup_clausec_request_signatures = function
| [] -> []
| p :: dl' ->
  let (n, f) = p in
  (match f.functionc_sig.sigc_params with
   | [] -> lookup_clausec_request_signatures dl'
   | _ :: l ->
     (match l with
      | [] -> lookup_clausec_request_signatures dl'
      | _ :: l0 ->
        (match l0 with
         | [] -> lookup_clausec_request_signatures dl'
         | _ :: l1 ->
           (match l1 with
            | [] -> lookup_clausec_request_signatures dl'
            | p0 :: l2 ->
              let (_, l3) = p0 in
              (match l3 with
               | ErgoTypeClassRef (_, _) ->
                 (match l2 with
                  | [] ->
                    (n,
                      f.functionc_sig) :: (lookup_clausec_request_signatures
                                            dl')
                  | _ :: _ -> lookup_clausec_request_signatures dl')
               | _ -> lookup_clausec_request_signatures dl')))))

(** val lookup_contractc_request_signatures :
    ergoc_contract -> (local_name * sigc) list **)

let lookup_contractc_request_signatures c =
  lookup_clausec_request_signatures c.contractc_clauses
