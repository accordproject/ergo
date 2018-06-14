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

(** Translates contract logic to calculus *)

Require Import String.
Require Import List.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.ErgoNNRC.Lang.ErgoNNRC.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Translation.ErgoNNRCtoJavaScript.

Section ErgoNNRCtoJavaScriptCicero.
  Local Open Scope string_scope.

  Definition accord_annotation
             (clause_name:string)
             (request_type:string)
             (response_type:string)
             (emits_type:string)
             (eol:string)
             (quotel:string) :=
    "/**" ++ eol
          ++ " * Execute the smart clause" ++ eol
          ++ " * @param {Context} context - the Accord context" ++ eol
          ++ " * @param {" ++ request_type ++ "} context.request - the incoming request" ++ eol
          ++ " * @param {" ++ response_type ++ "} context.response - the response" ++ eol
          ++ " * @param {" ++ emits_type ++ "} context.emit - the emitted events" ++ eol
          ++ (if string_dec clause_name clause_init_name then " * @AccordClauseLogicInit" else " * @AccordClauseLogic") ++ eol
          ++ " */" ++ eol.

  (** Note: this adjusts the external interface to that currently expected in Cicero. Namely:
- This serialized/deserialized CTO objects to/from JSON
- This applies the result from the functional call to the call as effects to the input context
- This turns an error response into a JavaScript exception
*)
  Definition wrapper_function
             (fun_name:string)
             (request_type:string)
             (response_type:string)
             (emits_type:string)
             (contract_name:string)
             (clause_name:string)
             (eol:string)
             (quotel:string) : string :=
    let state_init :=
        if string_dec clause_name clause_init_name
        then
          "{ '$class': 'org.accordproject.cicero.contract.AccordContractState', 'stateId' : 'org.accordproject.cicero.contract.AccordContractState#1' }"
        else
          "serializer.toJSON(context.state,{permitResourcesForRelationships:true})"
    in
    (accord_annotation
       clause_name
       request_type
       response_type
       emits_type
       eol
       quotel)
      ++ "function " ++ fun_name ++ "(context) {" ++ eol
      ++ "  let pcontext = { 'request' : serializer.toJSON(context.request,{permitResourcesForRelationships:true}), 'state': " ++ state_init ++ ", 'contract': serializer.toJSON(context.contract,{permitResourcesForRelationships:true}), 'emit': context.emit, 'now': context.now};" ++ eol
      ++ "    let result = new " ++ contract_name ++ "()." ++ clause_name ++ "(pcontext);" ++ eol
      ++ "  if (result.hasOwnProperty('left')) {" ++ eol
      ++ "    //logger.info('ergo result'+JSON.stringify(result))" ++ eol
      ++ "    context.response = serializer.fromJSON(result.left.response, {validate: false, acceptResourcesForRelationships: true},{permitResourcesForRelationships:true});" ++ eol
      ++ "    context.state = serializer.fromJSON(result.left.state, {validate: false, acceptResourcesForRelationships: true});" ++ eol
      ++ "    let emitResult = [];" ++ eol
      ++ "    for (let i = 0; i < result.left.emit.length; i++) {" ++ eol
      ++ "      emitResult.push(serializer.fromJSON(result.left.emit[i], {validate: false, acceptResourcesForRelationships: true}));" ++ eol
      ++ "    }" ++ eol
      ++ "    context.emit = emitResult;" ++ eol
      ++ "    return context;" ++ eol
      ++ "  } else {" ++ eol
      ++ "    throw new Error(result.right);" ++ eol
      ++ "  }" ++ eol
      ++ "}" ++ eol.

  Definition apply_wrapper_function
             (contract_name:string)
             (signature:string * string * string * string)
             (eol:string)
             (quotel:string) : ErgoCodeGen.javascript :=
    let '(clause_name, request_type, response_type, emits_type) := signature in
    let fun_name := contract_name ++ "_" ++ clause_name in
    wrapper_function
      fun_name request_type response_type emits_type contract_name clause_name eol quotel.
  
  Definition wrapper_functions
             (contract_name:string)
             (signatures:list (string * string * string * string))
             (eol:string)
             (quotel:string) : ErgoCodeGen.javascript :=
    String.concat eol (List.map (fun sig => apply_wrapper_function contract_name sig eol quotel) signatures).

  Definition javascript_of_package_with_dispatch
             (contract_name:string)
             (signatures:list (string * string * string * string))
             (p:nnrc_package)
             (eol:string)
             (quotel:string) : ErgoCodeGen.javascript :=
    (preamble eol) ++ eol
                   ++ (wrapper_functions contract_name signatures eol quotel)
                   ++ (javascript_of_declarations p.(packagen_declarations) 0 0 eol quotel)
                   ++ (postamble eol).

  Fixpoint filter_signatures (namespace:string) (sigs:list cto_signature) : list (string * string * string * string) :=
    match sigs with
    | nil => nil
    | sig :: rest =>
      if (string_dec sig.(cto_signature_name) clause_main_name)
      then
        filter_signatures namespace rest
      else
        let fname := sig.(cto_signature_name) in
        let params := sig.(cto_signature_params) in
        let outtype := sig.(cto_signature_output) in
        let emitstype := sig.(cto_signature_emits) in
        match params with
        | nil => filter_signatures namespace rest
        | (_,reqtype)::nil =>
          match reqtype, outtype, emitstype with
          | CTOClassRef reqname, CTOClassRef outname, Some (CTOClassRef emitsname) =>
            let qreqname := absolute_name_of_name_ref namespace reqname in
            let qoutname := absolute_name_of_name_ref namespace outname in
            let qemitsname := absolute_name_of_name_ref namespace emitsname in
            (fname,qreqname,qoutname,qemitsname) :: (filter_signatures namespace rest)
          | CTOClassRef reqname, CTOClassRef outname, None =>
            let qreqname := absolute_name_of_name_ref namespace reqname in
            let qoutname := absolute_name_of_name_ref namespace outname in
            let qemitsname := event_type in
            (fname,qreqname,qoutname,qemitsname) :: (filter_signatures namespace rest)
          | _, _, _ =>
            filter_signatures namespace rest
          end
        | _ :: _ => filter_signatures namespace rest
        end
    end.

  Definition ergoc_package_to_javascript_cicero
             (coname:string)
             (sigs: list cto_signature)
             (p:nnrc_package) : ErgoCodeGen.javascript :=
    javascript_of_package_with_dispatch
      coname
      (filter_signatures p.(packagen_namespace) sigs)
      p
      ErgoCodeGen.javascript_eol_newline
      ErgoCodeGen.javascript_quotel_double.

End ErgoNNRCtoJavaScriptCicero.

