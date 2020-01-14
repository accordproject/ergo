open Datatypes
open Ergo
open ErgoType
open List0
open Names
open Provenance
open Result0
open String0

(** val toDraftClause :
    provenance -> char list -> laergo_expr -> laergo_clause **)

let toDraftClause prov name template =
  { clause_annot = prov; clause_name = name; clause_sig =
    { type_signature_annot = prov; type_signature_params = [];
    type_signature_output = (Some (ErgoTypeString prov));
    type_signature_emits = None }; clause_body = (Some (SReturn (prov,
    (ECallFun (prov,
    ('o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::('.'::('t'::('o'::('T'::('e'::('x'::('t'::[])))))))))))))))))))))))))))))))))))),
    (template :: [])))))) }

(** val add_template_to_clauses :
    provenance -> (char list * laergo_expr) list -> laergo_clause list ->
    laergo_clause list **)

let add_template_to_clauses prov template cl =
  app cl (map (fun xy -> toDraftClause prov (fst xy) (snd xy)) template)

(** val add_template_to_contract :
    (char list * laergo_expr) list -> laergo_contract -> (provenance,
    provenance, absolute_name) ergo_contract **)

let add_template_to_contract template c =
  { contract_annot = c.contract_annot; contract_template =
    c.contract_template; contract_state = c.contract_state;
    contract_clauses =
    (add_template_to_clauses c.contract_annot template c.contract_clauses) }

(** val add_template_to_declaration :
    (char list * laergo_expr) list -> laergo_declaration -> laergo_declaration **)

let add_template_to_declaration template decl = match decl with
| DContract (a, ln, c) ->
  DContract (a, ln, (add_template_to_contract template c))
| _ -> decl

(** val add_template_to_module :
    (char list * laergo_expr) list -> laergo_module -> (provenance,
    provenance, absolute_name) ergo_module **)

let add_template_to_module template main =
  { module_annot = main.module_annot; module_file = main.module_file;
    module_prefix = main.module_prefix; module_namespace =
    main.module_namespace; module_declarations =
    (map (add_template_to_declaration template) main.module_declarations) }

(** val template_of_ergo_declaration :
    laergo_declaration -> (char list * char list) list **)

let template_of_ergo_declaration = function
| DType (_, tdecl) ->
  let name = tdecl.type_declaration_name in
  (match tdecl.type_declaration_type with
   | ErgoTypeAsset (_, e, _) ->
     (match e with
      | Some tname -> (name, tname) :: []
      | None -> [])
   | _ -> [])
| _ -> []

(** val template_of_ergo_declarations :
    laergo_declaration list -> (char list * char list) list **)

let template_of_ergo_declarations decls =
  List0.concat (map template_of_ergo_declaration decls)

(** val template_of_ergo_module :
    laergo_module -> (char list * char list) list **)

let template_of_ergo_module emod =
  template_of_ergo_declarations emod.module_declarations

(** val template_of_ergo_modules :
    laergo_module list -> (char list * char list) list **)

let template_of_ergo_modules emods =
  List0.concat (map template_of_ergo_module emods)

(** val find_template :
    provenance -> laergo_module list -> laergo_type eresult **)

let find_template prov emods =
  let decls = template_of_ergo_modules emods in
  let templateType_cond = fun templateType x ->
    let rel = snd x in if string_dec rel templateType then true else false
  in
  let templates =
    filter (templateType_cond default_contract_absolute_name) decls
  in
  (match templates with
   | [] ->
     let templates0 =
       filter (templateType_cond default_clause_absolute_name) decls
     in
     (match templates0 with
      | [] -> template_type_not_found_error prov
      | p :: l ->
        let (name, _) = p in
        (match l with
         | [] -> esuccess (ErgoTypeClassRef (prov, name)) []
         | _ :: _ ->
           more_than_one_template_type_error prov
             (concat (','::[]) (map fst templates0))))
   | p :: l ->
     let (name, _) = p in
     (match l with
      | [] -> esuccess (ErgoTypeClassRef (prov, name)) []
      | _ :: _ ->
        more_than_one_template_type_error prov
          (concat (','::[]) (map fst templates))))

(** val empty_main :
    provenance -> char list -> laergo_module list -> laergo_module eresult **)

let empty_main prov fname emods =
  elift (fun template -> { module_annot = prov; module_file = fname;
    module_prefix = ('l'::('o'::('g'::('i'::('c'::[]))))); module_namespace =
    ('E'::('m'::('p'::('t'::('y'::[]))))); module_declarations = ((DContract
    (prov, ('E'::('r'::('g'::('o'::[])))), { contract_annot = prov;
    contract_template = template; contract_state = None; contract_clauses =
    [] })) :: []) }) (find_template prov emods)
