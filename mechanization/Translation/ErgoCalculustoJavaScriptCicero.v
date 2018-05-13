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
Require Import ErgoSpec.Ergo.Lang.ErgoBase.
Require Import ErgoSpec.ErgoCalculus.Lang.ErgoCalculus.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Translation.ErgoCalculustoJavaScript.

Section ErgoCalculustoJavaScriptCicero.
  Local Open Scope string_scope.
  Definition dispatch_preamble
             (coname:string)
             (request:string)
             (response:string)
             (eol:string)
             (quotel:string) :=
    "/**" ++ eol
          ++ " * Execute the smart clause" ++ eol
          ++ " * @param {Context} context - the Accord context" ++ eol
          ++ " * @param {" ++ request ++ "} context.request - the incoming request" ++ eol
          ++ " * @param {" ++ response ++ "} context.response - the response" ++ eol
          ++ " * @AccordClauseLogic" ++ eol
          ++ " */" ++ eol
          ++ "function __dispatch(contract,request,state,now) {" ++ eol
          ++ "  let context = { 'request' : serializer.toJSON(request), 'state': state, 'contract': contract, 'now': now};" ++ eol
          ++ "  let result = new " ++ coname ++ "()." ++ clause_main_name ++ "(context);" ++ eol
          ++ "  if (result.hasOwnProperty('left')) {" ++ eol
          ++ "    return result.left;" ++ eol
          ++ "  } else {" ++ eol
          ++ "    return { 'response' : serializer.fromJSON(result.right.response), 'state' :result.right.state, 'emit' : result.right.emit };" ++ eol
          ++ "  }" ++ eol
          ++ "}" ++ eol.

  Definition javascript_of_package_with_dispatch
             (coname:string)
             (request:string)
             (response:string)
             (p:ergoc_package)
             (eol:string)
             (quotel:string) : ErgoCodeGen.ergoc_javascript :=
    (preamble eol) ++ eol
                   ++ (dispatch_preamble coname request response eol quotel) ++ eol
                   ++ (javascript_of_declarations p.(package_declarations) 0 0 eol quotel)
                   ++ (postamble eol).

  Definition ergoc_package_to_javascript_cicero
             (coname:string)
             (p:ergoc_package) : ErgoCodeGen.ergoc_javascript :=
    javascript_of_package_with_dispatch
      coname
      CTO.request_type
      CTO.response_type
      p
      ErgoCodeGen.ergoc_javascript_eol_newline
      ErgoCodeGen.ergoc_javascript_quotel_double.

End ErgoCalculustoJavaScriptCicero.

