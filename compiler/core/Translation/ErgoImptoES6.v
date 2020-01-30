(*
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

(** Translates ErgoNNRC to JavaScript *)

Require Import String.
Require Import List.

Require Import Qcert.JavaScriptAst.JavaScriptAstRuntime.
Require Import Qcert.Driver.CompDriver.
Require Import ErgoSpec.Version.
Require Import ErgoSpec.Utils.Misc.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Types.ErgoType.
Require Import ErgoSpec.ErgoImp.Lang.ErgoImp.
Require Import ErgoSpec.Backend.QLib.

Section Annotations.
  Local Open Scope nstring_scope.

  Definition accord_annotation
             (generated:bool)
             (clause_name:string)
             (request_type:string)
             (response_type:string)
             (emit_type:string)
             (state_type:string)
             (eol:nstring)
             (quotel:nstring) : nstring :=
    if generated
    then ^""
    else
      eol +++
      ^"/**" +++ eol
             +++ ^" * Execute the smart clause" +++ eol
             +++ ^" * @param {Context} context - the Accord context" +++ eol
             +++ ^" * @param {" +++ ^request_type +++ ^"} context.request - the incoming request" +++ eol
             +++ ^" * @param {" +++ ^response_type +++ ^"} context.response - the response" +++ eol
             +++ ^" * @param {" +++ ^emit_type +++ ^"} context.emit - the emitted events" +++ eol
             +++ ^" * @param {" +++ ^state_type +++ ^"} context.state - the state" +++ eol
             +++ ^" */" +++ eol.

End Annotations.

Section ErgoImptoES6.
  Local Open Scope list_scope.

  Context {bm:brand_model}.

  Section ToJsAst.
    (** Single function *)
    Definition ergo_imp_function_to_javascript_ast
               (fname:string)
               (fbody:ergo_imp_lambda)
               (tname:option string) : js_ast :=
      let fnameSafe := QcertCodeGen.javascript_identifier_sanitizer (function_name_in_table tname fname) in
      QcertCodeGen.imp_function_to_javascript_ast fnameSafe fbody.

    (** Function table *)
    Definition ergo_imp_function_table_to_javascript_ast
               (cname:string)
               (ft:ergo_imp_function_table) : js_ast :=
      let cnameSafe := QcertCodeGen.javascript_identifier_sanitizer cname in
      QcertCodeGen.imp_function_table_to_javascript_ast cnameSafe ft.

    Definition preamble : js_ast :=
      (comment (" Generated using ergo version " ++ ergo_version ++ " "))
        :: strictmode
        :: (comment "eslint-disable no-unused-vars")
        :: (comment "eslint-disable no-undef")
        :: (comment "eslint-disable no-var")
        :: nil.

    Definition postamble : js_ast :=
      (comment "eslint-enable no-unused-vars")
        :: (comment "eslint-enable no-undef")
        :: nil.

    Definition ergo_imp_declaration_to_javascript_ast
               (decl : ergo_imp_declaration)   (* statement to translate *)
      : js_ast
      :=
        match decl with
        | DIFunc fname fbody => ergo_imp_function_to_javascript_ast fname fbody None
        | DIFuncTable cname ft => ergo_imp_function_table_to_javascript_ast cname ft
        end.

    Definition ergo_imp_declarations_to_javascript_ast (sl : list ergo_imp_declaration) : js_ast
      := List.concat (List.map ergo_imp_declaration_to_javascript_ast sl).

    Definition ergo_imp_module_to_javascript_ast
               (p:ergo_imp_module) : js_ast :=
      preamble ++ (QcertCodeGen.javascript_of_inheritance brand_relation_brands)
               ++ (ergo_imp_declarations_to_javascript_ast p.(modulei_declarations))
               ++ (postamble).

    Definition ergo_imp_module_to_javascript_top
               (inheritance: list (string*string))
               (p:ergo_imp_module) : QcertCodeGen.ejavascript :=
      js_ast_to_javascript (ergo_imp_module_to_javascript_ast p).

  End ToJsAst.

  Section Cicero. (* XXX Some of this should go away once we have a proper way to export the module interface *)
    Local Open Scope nstring_scope.

    (** Note: this adjusts the external interface to what is currently expected by Cicero. Namely:
- This serialized/deserialized ErgoType objects to/from JSON
- This applies the result from the functional call to the call as effects to the input context
- This turns an error response into a JavaScript exception
*)
    Definition wrapper_function_for_clause
               (generated:bool)
               (fun_name:string)
               (request_param:string)
               (request_type:string)
               (response_type:string)
               (emit_type:string)
               (state_type:string)
               (contract_name:string)
               (clause_name:string)
               (eol:nstring)
               (quotel:nstring) : nstring :=
      (accord_annotation
         generated
         clause_name
         request_type
         response_type
         emit_type
         state_type
         eol
         quotel)
        +++ eol
        +++ ^"function " +++ ^fun_name +++ ^"(context) {" +++ eol
        +++ ^"  let pcontext = Object.assign(context, { '" +++ ^request_param +++ ^"' : context.request });" +++ eol
        +++ ^"  return " +++ ^ contract_name +++ ^"." +++ ^ clause_name +++ ^"(pcontext);" +++ eol
        +++ ^"}".

    Definition wrapper_function_for_init
               (generated:bool)
               (fun_name:string)
               (response_type:string)
               (emit_type:string)
               (state_type:string)
               (contract_name:string)
               (eol:nstring)
               (quotel:nstring) : nstring :=
      let state_init := ^"{ '$class': 'org.accordproject.cicero.contract.AccordContractState', 'stateId' : 'org.accordproject.cicero.contract.AccordContractState#1' }" in
      eol +++ ^"function " +++ ^fun_name +++ ^"(context) {" +++ eol
          +++ ^"  let pcontext = Object.assign(context, { 'state': " +++ state_init +++ ^" });" +++ eol
          +++ ^"  return new " +++ ^contract_name +++ ^"().init(pcontext);" +++ eol
          +++ ^"}".

    Definition apply_wrapper_function
               (contract_name:string)
               (contract_state_type:string)
               (signature: string * string * string * string * string)
               (eol:nstring)
               (quotel:nstring) : nstring :=
      let '(clause_name, request_name, request_type, response_type, emit_type) := signature in
      let fun_name : string :=
          QcertCodeGen.javascript_identifier_sanitizer (contract_name ++ "_"%string ++ clause_name)
      in
      let cname : string :=
          QcertCodeGen.javascript_identifier_sanitizer contract_name
      in
      if string_dec clause_name clause_init_name
      then ^""
      else
        wrapper_function_for_clause
          false
          fun_name request_name request_type response_type emit_type contract_state_type cname clause_name eol quotel.
  
    Definition wrapper_functions
               (contract_name:string)
               (signatures:list (string * string * string * string * string) * string)
               (eol:nstring)
               (quotel:nstring) : nstring :=
      nstring_concat eol
                     (List.map (fun sig => apply_wrapper_function
                                             contract_name
                                             (snd signatures)
                                             sig
                                             eol
                                             quotel) (fst signatures)).

    Definition javascript_main_dispatch_and_init
               (contract_name:string)
               (eol:nstring)
               (quotel:nstring) : nstring :=
      let cname : string :=
          QcertCodeGen.javascript_identifier_sanitizer contract_name
      in
      ^"" +++ wrapper_function_for_clause true "__dispatch" "request" "org.accordproject.cicero.runtime.Request" "org.accordproject.cicero.runtime.Response" "org.accordproject.cicero.runtime.Emit" "org.accordproject.cicero.runtime.State" cname clause_main_name eol quotel
          +++ wrapper_function_for_init true "__init" "org.accordproject.cicero.runtime.Response" "org.accordproject.cicero.runtime.Emit" "org.accordproject.cicero.runtime.State" cname eol quotel.

    Definition javascript_of_module_with_dispatch
               (contract_name:string)
               (signatures:list (string * string * string * string * string) * string)
               (p:ergo_imp_module)
               (eol:nstring)
               (quotel:nstring) : nstring :=
      (QcertCodeGen.js_ast_to_javascript preamble) +++ eol
                   +++ (wrapper_functions contract_name signatures eol quotel)
                   +++ (ergo_imp_module_to_javascript_top brand_relation_brands p)
                   +++ (javascript_main_dispatch_and_init contract_name eol quotel)
                   +++ (QcertCodeGen.js_ast_to_javascript postamble).

    Fixpoint filter_signatures
             (namespace:string)
             (sigs:list (string * laergo_type_signature))
      : list (string * string * string * string * string) :=
      match sigs with
      | nil => nil
      | (fname,sig) :: rest =>
        if (string_dec fname clause_main_name)
        then
          filter_signatures namespace rest
        else
          let params := sig.(type_signature_params) in
          let outtype := sig.(type_signature_output) in
          let emitstype := sig.(type_signature_emits) in
          match params with
          | nil => filter_signatures namespace rest
          | (reqparam,reqtype)::nil =>
            match reqtype, outtype, emitstype with
            | ErgoTypeClassRef _ reqname, Some (ErgoTypeClassRef _ outname), Some (ErgoTypeClassRef _ emitsname) =>
              (fname,reqparam,reqname,outname,emitsname) :: (filter_signatures namespace rest)
            | ErgoTypeClassRef _ reqname, Some (ErgoTypeClassRef _ outname), None =>
              let emitsname := default_event_absolute_name in
              (fname,reqparam,reqname,outname,emitsname) :: (filter_signatures namespace rest)
            | _, _, _ =>
              filter_signatures namespace rest
            end
          | _ :: _ => filter_signatures namespace rest
          end
      end.

    Definition filter_signatures_with_state
               (namespace:string)
               (contract_state_type:option laergo_type)
               (sigs:list (string * ergo_type_signature))
      : list (string * string * string * string * string) * string :=
      match contract_state_type with
      | None => (filter_signatures namespace sigs, default_state_absolute_name)
      | Some (ErgoTypeClassRef _ statename) =>
        (filter_signatures namespace sigs, statename)
      | _ =>
        (nil, ""%string)
      end.

    Definition ergo_imp_module_to_es6
               (contract_name:string)
               (contract_state_type:option ergo_type)
               (sigs: list (string * ergo_type_signature))
               (p:ergo_imp_module) : QcertCodeGen.ejavascript :=
      javascript_of_module_with_dispatch
        contract_name
        (filter_signatures_with_state p.(modulei_namespace) contract_state_type sigs)
        p
        EmitUtil.neol_newline
        EmitUtil.nquotel_double.

  End Cicero.
End ErgoImptoES6.

