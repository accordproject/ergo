open Ast
open CTO
open Data
open Datatypes
open ErgoType
open List0
open Misc
open Names
open Provenance
open QLib
open Result0

type ('a, 'x, 'n) ergo_expr =
| EThis of 'a
| EThisContract of 'a
| EThisClause of 'a
| EThisState of 'a
| EVar of 'a * 'n
| EConst of 'a * data
| EText of 'a * ('a, 'x, 'n) ergo_expr list
| ENone of 'a
| ESome of 'a * ('a, 'x, 'n) ergo_expr
| EArray of 'a * ('a, 'x, 'n) ergo_expr list
| EUnaryOperator of 'a * ergo_unary_operator * ('a, 'x, 'n) ergo_expr
| EBinaryOperator of 'a * ergo_binary_operator * ('a, 'x, 'n) ergo_expr
   * ('a, 'x, 'n) ergo_expr
| EUnaryBuiltin of 'a * QcertOps.Unary.op * ('a, 'x, 'n) ergo_expr
| EBinaryBuiltin of 'a * QcertOps.Binary.op * ('a, 'x, 'n) ergo_expr
   * ('a, 'x, 'n) ergo_expr
| EIf of 'a * ('a, 'x, 'n) ergo_expr * ('a, 'x, 'n) ergo_expr
   * ('a, 'x, 'n) ergo_expr
| ELet of 'a * char list * ('x, 'n) ergo_type option * ('a, 'x, 'n) ergo_expr
   * ('a, 'x, 'n) ergo_expr
| EPrint of 'a * ('a, 'x, 'n) ergo_expr * ('a, 'x, 'n) ergo_expr
| ERecord of 'a * (char list * ('a, 'x, 'n) ergo_expr) list
| ENew of 'a * 'n * (char list * ('a, 'x, 'n) ergo_expr) list
| ECallFun of 'a * 'n * ('a, 'x, 'n) ergo_expr list
| ECallFunInGroup of 'a * 'n * char list * ('a, 'x, 'n) ergo_expr list
| EMatch of 'a * ('a, 'x, 'n) ergo_expr
   * (('a, 'n) ergo_pattern * ('a, 'x, 'n) ergo_expr) list
   * ('a, 'x, 'n) ergo_expr
| EForeach of 'a * (char list * ('a, 'x, 'n) ergo_expr) list
   * ('a, 'x, 'n) ergo_expr option * ('a, 'x, 'n) ergo_expr
| EAs of 'a * char list * ('a, 'x, 'n) ergo_expr

(** val expr_annot : ('a1, 'a2, 'a3) ergo_expr -> 'a1 **)

let expr_annot = function
| EThis a -> a
| EThisContract a -> a
| EThisClause a -> a
| EThisState a -> a
| EVar (a, _) -> a
| EConst (a, _) -> a
| EText (a, _) -> a
| ENone a -> a
| ESome (a, _) -> a
| EArray (a, _) -> a
| EUnaryOperator (a, _, _) -> a
| EBinaryOperator (a, _, _, _) -> a
| EUnaryBuiltin (a, _, _) -> a
| EBinaryBuiltin (a, _, _, _) -> a
| EIf (a, _, _, _) -> a
| ELet (a, _, _, _, _) -> a
| EPrint (a, _, _) -> a
| ERecord (a, _) -> a
| ENew (a, _, _) -> a
| ECallFun (a, _, _) -> a
| ECallFunInGroup (a, _, _, _) -> a
| EMatch (a, _, _, _) -> a
| EForeach (a, _, _, _) -> a
| EAs (a, _, _) -> a

type ('a, 'x, 'n) ergo_stmt =
| SReturn of 'a * ('a, 'x, 'n) ergo_expr
| SFunReturn of 'a * ('a, 'x, 'n) ergo_expr
| SThrow of 'a * ('a, 'x, 'n) ergo_expr
| SCallClause of 'a * ('a, 'x, 'n) ergo_expr * char list
   * ('a, 'x, 'n) ergo_expr list
| SCallContract of 'a * ('a, 'x, 'n) ergo_expr * ('a, 'x, 'n) ergo_expr list
| SSetState of 'a * ('a, 'x, 'n) ergo_expr * ('a, 'x, 'n) ergo_stmt
| SSetStateDot of 'a * char list * ('a, 'x, 'n) ergo_expr
   * ('a, 'x, 'n) ergo_stmt
| SEmit of 'a * ('a, 'x, 'n) ergo_expr * ('a, 'x, 'n) ergo_stmt
| SLet of 'a * char list * ('a, 'n) ergo_type option * ('a, 'x, 'n) ergo_expr
   * ('a, 'x, 'n) ergo_stmt
| SPrint of 'a * ('a, 'x, 'n) ergo_expr * ('a, 'x, 'n) ergo_stmt
| SIf of 'a * ('a, 'x, 'n) ergo_expr * ('a, 'x, 'n) ergo_stmt
   * ('a, 'x, 'n) ergo_stmt
| SEnforce of 'a * ('a, 'x, 'n) ergo_expr * ('a, 'x, 'n) ergo_stmt option
   * ('a, 'x, 'n) ergo_stmt
| SMatch of 'a * ('a, 'x, 'n) ergo_expr
   * (('a, 'n) ergo_pattern * ('a, 'x, 'n) ergo_stmt) list
   * ('a, 'x, 'n) ergo_stmt

type ('a, 'x, 'n) ergo_function = { function_annot : 'a;
                                    function_sig : ('a, 'n)
                                                   ergo_type_signature;
                                    function_body : ('a, 'x, 'n) ergo_expr
                                                    option }

type ('a, 'x, 'n) ergo_clause = { clause_annot : 'a;
                                  clause_name : local_name;
                                  clause_sig : ('a, 'n) ergo_type_signature;
                                  clause_body : ('a, 'x, 'n) ergo_stmt option }

type ('a, 'x, 'n) ergo_contract = { contract_annot : 'a;
                                    contract_template : ('a, 'n) ergo_type;
                                    contract_state : ('a, 'n) ergo_type option;
                                    contract_clauses : ('a, 'x, 'n)
                                                       ergo_clause list }

type ('a, 'x, 'n) ergo_declaration =
| DNamespace of 'a * namespace_name
| DImport of 'a * 'a import_decl
| DType of 'a * ('a, 'n) ergo_type_declaration
| DStmt of 'a * ('a, 'x, 'n) ergo_stmt
| DConstant of 'a * local_name * ('a, 'n) ergo_type option
   * ('a, 'x, 'n) ergo_expr
| DFunc of 'a * local_name * ('a, 'x, 'n) ergo_function
| DContract of 'a * local_name * ('a, 'x, 'n) ergo_contract
| DSetContract of 'a * 'n * ('a, 'x, 'n) ergo_expr

type ('a, 'x, 'n) ergo_module = { module_annot : 'a; module_file : char list;
                                  module_prefix : char list;
                                  module_namespace : namespace_name;
                                  module_declarations : ('a, 'x, 'n)
                                                        ergo_declaration list }

type ('a, 'x, 'n) ergo_input =
| InputErgo of ('a, 'x, 'n) ergo_module
| InputCTO of ('a, 'n) cto_package

type ('a, 'x) rergo_expr = ('a, 'x, relative_name) ergo_expr

type ('a, 'x) rergo_stmt = ('a, 'x, relative_name) ergo_stmt

type lrergo_expr = (provenance, provenance, relative_name) ergo_expr

type lrergo_stmt = (provenance, provenance, relative_name) ergo_stmt

type lrergo_function = (provenance, provenance, relative_name) ergo_function

type lrergo_clause = (provenance, provenance, relative_name) ergo_clause

type lrergo_contract = (provenance, provenance, relative_name) ergo_contract

type lrergo_declaration =
  (provenance, provenance, relative_name) ergo_declaration

type lrergo_module = (provenance, provenance, relative_name) ergo_module

type lrergo_input = (provenance, provenance, relative_name) ergo_input

type laergo_expr = (provenance, provenance, absolute_name) ergo_expr

type laergo_stmt = (provenance, provenance, absolute_name) ergo_stmt

type laergo_function = (provenance, provenance, absolute_name) ergo_function

type laergo_clause = (provenance, provenance, absolute_name) ergo_clause

type laergo_contract = (provenance, provenance, absolute_name) ergo_contract

type laergo_declaration =
  (provenance, provenance, absolute_name) ergo_declaration

type laergo_module = (provenance, provenance, absolute_name) ergo_module

(** val lookup_clause_signatures :
    laergo_clause list -> (local_name * (provenance, absolute_name)
    ergo_type_signature) list **)

let rec lookup_clause_signatures = function
| [] -> []
| cl :: dl' ->
  (cl.clause_name, cl.clause_sig) :: (lookup_clause_signatures dl')

(** val lookup_contract_signatures :
    (provenance, provenance, absolute_name) ergo_contract ->
    (local_name * (provenance, absolute_name) ergo_type_signature) list **)

let lookup_contract_signatures c =
  lookup_clause_signatures c.contract_clauses

(** val contract_of_declaration :
    laergo_declaration -> (absolute_name * laergo_contract) option **)

let contract_of_declaration = function
| DContract (_, cn, c) -> Some (cn, c)
| _ -> None

(** val lookup_contracts_in_declarations :
    laergo_declaration list -> (absolute_name * laergo_contract) list **)

let lookup_contracts_in_declarations dl =
  filter_some contract_of_declaration dl

(** val lookup_single_contract_in_declarations :
    provenance -> laergo_declaration list ->
    (absolute_name * laergo_contract) eresult **)

let lookup_single_contract_in_declarations prov dl =
  match lookup_contracts_in_declarations dl with
  | [] -> should_have_one_contract_error prov
  | c :: l ->
    (match l with
     | [] -> esuccess c []
     | _ :: _ -> should_have_one_contract_error prov)

(** val lookup_single_contract :
    laergo_module -> (absolute_name * laergo_contract) eresult **)

let lookup_single_contract p =
  lookup_single_contract_in_declarations p.module_annot p.module_declarations

(** val get_type_decls :
    laergo_declaration list -> laergo_type_declaration list **)

let rec get_type_decls = function
| [] -> []
| l :: rest ->
  (match l with
   | DType (_, td) -> td :: (get_type_decls rest)
   | _ -> get_type_decls rest)

(** val module_get_type_decls :
    laergo_module -> laergo_type_declaration list **)

let module_get_type_decls m =
  get_type_decls m.module_declarations

(** val modules_get_type_decls :
    laergo_module list -> laergo_type_declaration list **)

let modules_get_type_decls m =
  concat (map module_get_type_decls m)

(** val either_from_enum_values :
    char list list -> (char list * data) list **)

let rec either_from_enum_values = function
| [] -> []
| x :: enum_values' ->
  let new_values = either_from_enum_values enum_values' in
  (x, (Coq_dleft (Coq_dstring
  x))) :: (map (fun xy -> ((fst xy), (Coq_dright (snd xy)))) new_values)

(** val globals_from_enum :
    provenance -> (char list * char list list) ->
    ((char list * laergo_expr) * data) list **)

let globals_from_enum prov = function
| (enum_name, enum_values) ->
  map (fun xy ->
    let d = Coq_dbrand ((enum_name :: []), (snd xy)) in
    (((fst xy), (EConst (prov, d))), d)) (either_from_enum_values enum_values)
