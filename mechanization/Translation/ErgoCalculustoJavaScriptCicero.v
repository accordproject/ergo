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
Require Import ErgoSpec.Ergo.Lang.ErgoBase.
Require Import ErgoSpec.ErgoCalculus.Lang.ErgoCalculus.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Translation.ErgoCalculustoJavaScript.

Section ErgoCalculustoJavaScriptCicero.
  Local Open Scope string_scope.

  Definition accord_annotation
             (request_type:string)
             (response_type:string)
             (eol:string)
             (quotel:string) :=
    "/**" ++ eol
          ++ " * Execute the smart clause" ++ eol
          ++ " * @param {Context} context - the Accord context" ++ eol
          ++ " * @param {" ++ request_type ++ "} context.request - the incoming request" ++ eol
          ++ " * @param {" ++ response_type ++ "} context.response - the response" ++ eol
          ++ " * @AccordClauseLogic" ++ eol
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
             (contract_name:string)
             (clause_name:string)
             (eol:string)
             (quotel:string) : string :=
    (accord_annotation
       request_type
       response_type
       eol
       quotel)
      ++ "function " ++ fun_name ++ "(context) {" ++ eol
      ++ "  let pcontext = { 'request' : serializer.toJSON(context.request), 'state': context.state, 'contract': context.contract, 'now': context.now};" ++ eol
      ++ "  let result = new " ++ contract_name ++ "()." ++ clause_name ++ "(pcontext);" ++ eol
      ++ "  if (result.hasOwnProperty('left')) {" ++ eol
      ++ "    context.response = serializer.fromJSON(result.left.response);" ++ eol
      ++ "    context.state = result.left.state;" ++ eol
      ++ "    context.emit = result.left.emit;" ++ eol
      ++ "    return context;" ++ eol
      ++ "  } else {" ++ eol
      ++ "    throw new Error(result.right);" ++ eol
      ++ "  }" ++ eol
      ++ "}" ++ eol.

  Definition dispatch_function
             (contract_name:string)
             (eol:string)
             (quotel:string) : string :=
    (accord_annotation
       CTO.request_type
       CTO.response_type
       eol
       quotel)
      ++ "function __dispatch(contract,request,state,now) {" ++ eol
      ++ "  let context = { 'request' : serializer.toJSON(request), 'state': state, 'contract': contract, 'now': now};" ++ eol
      ++ "  let result = new " ++ contract_name ++ "()." ++ clause_main_name ++ "(context);" ++ eol
      ++ "  if (result.hasOwnProperty('left')) {" ++ eol
      ++ "    return { 'response' : serializer.fromJSON(result.left.response), 'state' :result.left.state, 'emit' : result.left.emit };" ++ eol
      ++ "  } else {" ++ eol
      ++ "    return { 'error' : result.right };" ++ eol
      ++ "  }" ++ eol
      ++ "}" ++ eol.

  Definition apply_wrapper_function
             (contract_name:string)
             (signature:string * string * string)
             (eol:string)
             (quotel:string) : ErgoCodeGen.ergoc_javascript :=
    let '(clause_name, request_type, response_type) := signature in
    let fun_name := contract_name ++ "_" ++ clause_name in
    wrapper_function
      fun_name request_type response_type contract_name clause_name eol quotel.
  
  Definition wrapper_functions
             (contract_name:string)
             (signatures:list (string * string * string))
             (eol:string)
             (quotel:string) : ErgoCodeGen.ergoc_javascript :=
    String.concat eol (List.map (fun sig => apply_wrapper_function contract_name sig eol quotel) signatures).

  Definition javascript_of_package_with_dispatch
             (contract_name:string)
             (signatures:list (string * string * string))
             (p:ergoc_package)
             (eol:string)
             (quotel:string) : ErgoCodeGen.ergoc_javascript :=
    (preamble eol) ++ eol
                   ++ (wrapper_functions contract_name signatures eol quotel)
                   (* ++ (dispatch_function contract_name eol quotel) ++ eol *)
                   ++ (javascript_of_declarations p.(package_declarations) 0 0 eol quotel)
                   ++ (postamble eol).

  Fixpoint filter_signatures (namespace:string) (sigs:list signature) : list (string * string * string) :=
    match sigs with
    | nil => nil
    | sig :: rest =>
      let '(fname, params, outtype) := sig in
      match params with
      | nil => filter_signatures namespace rest
      | (_,reqtype)::nil =>
        match reqtype, outtype with
        | CTOClassRef reqname, CTOClassRef outname =>
          let qreqname := absolute_ref_of_relative_ref namespace reqname in
          let qoutname := absolute_ref_of_relative_ref namespace outname in
          (fname,qreqname,qoutname) :: (filter_signatures namespace rest)
        | _, _ =>
          filter_signatures namespace rest
        end
      | _ :: _ => filter_signatures namespace rest
      end
    end.

  Definition ergoc_package_to_javascript_cicero
             (coname:string)
             (sigs: list signature)
             (p:ergoc_package) : ErgoCodeGen.ergoc_javascript :=
    javascript_of_package_with_dispatch
      coname
      (filter_signatures p.(package_namespace) sigs)
      p
      ErgoCodeGen.ergoc_javascript_eol_newline
      ErgoCodeGen.ergoc_javascript_quotel_double.

End ErgoCalculustoJavaScriptCicero.

