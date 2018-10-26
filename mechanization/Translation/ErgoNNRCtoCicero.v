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

Require Import ErgoSpec.Common.Utils.Misc.
Require Import ErgoSpec.Common.Utils.Result.
Require Import ErgoSpec.Common.Utils.Names.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.ErgoNNRC.Lang.ErgoNNRC.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Translation.ErgoNNRCtoJavaScript.

Section ErgoNNRCtoCicero.
  Local Open Scope string_scope.

  Definition accord_annotation
             (clause_name:string)
             (request_type:string)
             (response_type:string)
             (emit_type:string)
             (state_type:string)
             (eol:string)
             (quotel:string) :=
    "/**" ++ eol
          ++ " * Execute the smart clause" ++ eol
          ++ " * @param {Context} context - the Accord context" ++ eol
          ++ " * @param {" ++ request_type ++ "} context.request - the incoming request" ++ eol
          ++ " * @param {" ++ response_type ++ "} context.response - the response" ++ eol
          ++ " * @param {" ++ emit_type ++ "} context.emit - the emitted events" ++ eol
          ++ " * @param {" ++ state_type ++ "} context.state - the state" ++ eol
          ++ (if string_dec clause_name clause_init_name then " * @AccordClauseLogicInit" ++ eol else "")
          ++ " * @AccordClauseLogic" ++ eol
          ++ " */" ++ eol.

  (** Note: this adjusts the external interface to that currently expected in Cicero. Namely:
- This serialized/deserialized ErgoType objects to/from JSON
- This applies the result from the functional call to the call as effects to the input context
- This turns an error response into a JavaScript exception
*)
  Definition wrapper_function
             (fun_name:string)
             (request_param:string)
             (request_type:string)
             (response_type:string)
             (emit_type:string)
             (state_type:string)
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
       emit_type
       state_type
       eol
       quotel)
      ++ "function " ++ fun_name ++ "(context) {" ++ eol
      ++ "  let pcontext = { '" ++ request_param ++ "' : serializer.toJSON(context.request,{permitResourcesForRelationships:true}), 'state': " ++ state_init ++ ", 'contract': serializer.toJSON(context.contract,{permitResourcesForRelationships:true}), 'emit': context.emit, 'now': context.now};" ++ eol
      ++ "  //logger.info('ergo context: '+JSON.stringify(pcontext))" ++ eol
      ++ "  let result = new " ++ ErgoCodeGen.javascript_identifier_sanitizer contract_name ++ "()." ++ ErgoCodeGen.javascript_identifier_sanitizer clause_name ++ "(pcontext);" ++ eol
      ++ "  if (result.hasOwnProperty('left')) {" ++ eol
      ++ "    //logger.info('ergo result: '+JSON.stringify(result))" ++ eol
      ++ "    context.response = serializer.fromJSON(result.left.response, {validate: false, acceptResourcesForRelationships: true},{permitResourcesForRelationships:true});" ++ eol
      ++ "    context.state = serializer.fromJSON(result.left.state, {validate: false, acceptResourcesForRelationships: true});" ++ eol
      ++ "    let emitResult = [];" ++ eol
      ++ "    for (let i = 0; i < result.left.emit.length; i++) {" ++ eol
      ++ "      emitResult.push(serializer.fromJSON(result.left.emit[i], {validate: false, acceptResourcesForRelationships: true}));" ++ eol
      ++ "    }" ++ eol
      ++ "    context.emit = emitResult;" ++ eol
      ++ "    return context;" ++ eol
      ++ "  } else {" ++ eol
      ++ "    throw new Error(result.right.message);" ++ eol
      ++ "  }" ++ eol
      ++ "}" ++ eol.

  Definition apply_wrapper_function
             (contract_name:string)
             (contract_state_type:string)
             (signature: string * string * string * string * string)
             (eol:string)
             (quotel:string) : ErgoCodeGen.javascript :=
    let '(clause_name, request_name, request_type, response_type, emit_type) := signature in
    let fun_name := ErgoCodeGen.javascript_identifier_sanitizer contract_name ++ "_" ++ ErgoCodeGen.javascript_identifier_sanitizer clause_name in
    wrapper_function
      fun_name request_name request_type response_type emit_type contract_state_type contract_name clause_name eol quotel.
  
  Definition wrapper_functions
             (contract_name:string)
             (signatures:list (string * string * string * string * string) * string)
             (eol:string)
             (quotel:string) : ErgoCodeGen.javascript :=
    String.concat eol
                  (List.map (fun sig => apply_wrapper_function
                                          contract_name
                                          (snd signatures)
                                          sig
                                          eol
                                          quotel) (fst signatures)).
  Definition javascript_main_dispatch_and_init
             (contract_name:string)
             (eol:string)
             (quotel:string) : ErgoCodeGen.javascript :=
    "" ++ "const contract = new " ++ ErgoCodeGen.javascript_identifier_sanitizer contract_name ++ "();" ++ eol
       ++ "function dispatch(context) {" ++ eol
       ++ "  return contract.main(context);" ++ eol
       ++ "}" ++ eol
       ++ "function init(context) {" ++ eol
       ++ "  return contract.init(context);" ++ eol
       ++ "}" ++ eol.

  Definition javascript_of_module_with_dispatch
             (contract_name:string)
             (signatures:list (string * string * string * string * string) * string)
             (p:nnrc_module)
             (eol:string)
             (quotel:string) : ErgoCodeGen.javascript :=
    (preamble eol) ++ eol
                   ++ (wrapper_functions contract_name signatures eol quotel)
                   ++ (javascript_of_declarations ES6 p.(modulen_declarations) 0 0 eol quotel)
                   ++ (javascript_main_dispatch_and_init contract_name eol quotel)
                   ++ (postamble eol).

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
      (nil, "")
    end.

  Definition ergoc_module_to_cicero
             (contract_name:string)
             (contract_state_type:option ergo_type)
             (sigs: list (string * ergo_type_signature))
             (p:nnrc_module) : ErgoCodeGen.javascript :=
    javascript_of_module_with_dispatch
      contract_name
      (filter_signatures_with_state p.(modulen_namespace) contract_state_type sigs)
      p
      ErgoCodeGen.javascript_eol_newline
      ErgoCodeGen.javascript_quotel_double.

End ErgoNNRCtoCicero.

