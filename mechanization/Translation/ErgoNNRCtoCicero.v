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

Require Import ErgoSpec.Utils.Misc.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Types.ErgoType.
Require Import ErgoSpec.ErgoNNRC.Lang.ErgoNNRC.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Translation.ErgoNNRCtoJavaScript.

Section ErgoNNRCtoCicero.
  Local Open Scope string_scope.
  Local Open Scope estring_scope.

  Definition accord_annotation
             (generated:bool)
             (clause_name:string)
             (request_type:string)
             (response_type:string)
             (emit_type:string)
             (state_type:string)
             (eol:estring)
             (quotel:estring) : estring :=
    if generated
    then `""
    else
      `"/**" +++ eol
             +++ `" * Execute the smart clause" +++ eol
             +++ `" * @param {Context} context - the Accord context" +++ eol
             +++ `" * @param {" +++ `request_type +++ `"} context.request - the incoming request" +++ eol
             +++ `" * @param {" +++ `response_type +++ `"} context.response - the response" +++ eol
             +++ `" * @param {" +++ `emit_type +++ `"} context.emit - the emitted events" +++ eol
             +++ `" * @param {" +++ `state_type +++ `"} context.state - the state" +++ eol
             +++ `" */" +++ eol.

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
             (eol:estring)
             (quotel:estring) : estring :=
    (accord_annotation
       generated
       clause_name
       request_type
       response_type
       emit_type
       state_type
       eol
       quotel)
      +++ `"function " +++ `fun_name +++ `"(context) {" +++ eol
      +++ `"  let pcontext = { '" +++ `request_param +++ `"' : context.request, '__state': context.__state, '__contract': context.__contract, '__emit': context.__emit, '__now': context.__now, '__options': context.__options};" +++ eol
      +++ `"  //logger.info('ergo context: '+JSON.stringify(pcontext))" +++ eol
      +++ `"  return new " +++ `ErgoCodeGen.javascript_identifier_sanitizer contract_name +++ `"()." +++ `ErgoCodeGen.javascript_identifier_sanitizer clause_name +++ `"(pcontext);" +++ eol
      +++ `"}" +++ eol.

  Definition wrapper_function_for_init
             (generated:bool)
             (fun_name:string)
             (response_type:string)
             (emit_type:string)
             (state_type:string)
             (contract_name:string)
             (eol:estring)
             (quotel:estring) : estring :=
    let state_init := `"{ '$class': 'org.accordproject.cicero.contract.AccordContractState', 'stateId' : 'org.accordproject.cicero.contract.AccordContractState#1' }" in
    `"function " +++ `fun_name +++ `"(context) {" +++ eol
     +++ `"  let pcontext = { 'state': " +++ state_init +++ `", '__contract': context.__contract, '__emit': context.__emit, '__now': context.__now, '__options': context.__options};" +++ eol
     +++ `"  //logger.info('ergo context: '+JSON.stringify(pcontext))" +++ eol
     +++ `"  return new " +++ `ErgoCodeGen.javascript_identifier_sanitizer contract_name +++ `"().init(pcontext);" +++ eol
     +++ `"}" +++ eol.

  Definition apply_wrapper_function
             (contract_name:string)
             (contract_state_type:string)
             (signature: string * string * string * string * string)
             (eol:estring)
             (quotel:estring) : ErgoCodeGen.ejavascript :=
    let '(clause_name, request_name, request_type, response_type, emit_type) := signature in
    let fun_name : string :=
        ErgoCodeGen.javascript_identifier_sanitizer contract_name ++ "_"%string ++ ErgoCodeGen.javascript_identifier_sanitizer clause_name
    in
    if string_dec clause_name clause_init_name
    then `""
    else
      wrapper_function_for_clause false
                       fun_name request_name request_type response_type emit_type contract_state_type contract_name clause_name eol quotel.
  
  Definition wrapper_functions
             (contract_name:string)
             (signatures:list (string * string * string * string * string) * string)
             (eol:estring)
             (quotel:estring) : ErgoCodeGen.ejavascript :=
    econcat eol
            (List.map (fun sig => apply_wrapper_function
                                    contract_name
                                    (snd signatures)
                                    sig
                                    eol
                                    quotel) (fst signatures)).

  Definition javascript_main_dispatch_and_init
             (contract_name:string)
             (eol:estring)
             (quotel:estring) : ErgoCodeGen.ejavascript :=
    `"" +++ `"const contract = new " +++ `ErgoCodeGen.javascript_identifier_sanitizer contract_name +++ `"();" +++ eol
        +++ wrapper_function_for_clause true "__dispatch" "request" "org.accordproject.cicero.runtime.Request" "org.accordproject.cicero.runtime.Response" "org.accordproject.cicero.runtime.Emit" "org.accordproject.cicero.runtime.State" contract_name clause_main_name eol quotel
        +++ wrapper_function_for_init true "__init" "org.accordproject.cicero.runtime.Response" "org.accordproject.cicero.runtime.Emit" "org.accordproject.cicero.runtime.State" contract_name eol quotel.

  Definition javascript_of_module_with_dispatch
             (contract_name:string)
             (signatures:list (string * string * string * string * string) * string)
             (p:nnrc_module)
             (eol:estring)
             (quotel:estring) : ErgoCodeGen.ejavascript :=
    (preamble eol) +++ eol
                   +++ (wrapper_functions contract_name signatures eol quotel)
                   +++ (javascript_of_declarations ES6 p.(modulen_declarations) 0 0 eol quotel)
                   +++ (javascript_main_dispatch_and_init contract_name eol quotel)
                   +++ (postamble eol).

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
             (p:nnrc_module) : ErgoCodeGen.ejavascript :=
    javascript_of_module_with_dispatch
      contract_name
      (filter_signatures_with_state p.(modulen_namespace) contract_state_type sigs)
      p
      ErgoCodeGen.javascript_eol_newline
      ErgoCodeGen.javascript_quotel_double.

End ErgoNNRCtoCicero.

