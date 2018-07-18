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

(** Compilation paths *)

Require Import String.
Require Import List.

Require Import ErgoSpec.Backend.ForeignErgo.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Utils.EAstUtil.
Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.Ergo.Lang.ErgoExpand.
Require Import ErgoSpec.ErgoC.Lang.ErgoC.
Require Import ErgoSpec.ErgoC.Lang.ErgoCEvalContext.
Require Import ErgoSpec.ErgoC.Lang.ErgoCEval.
Require Import ErgoSpec.Translation.CTOtoErgo.
Require Import ErgoSpec.Translation.ErgoNameResolve.
Require Import ErgoSpec.Translation.ErgotoErgoC.
Require Import ErgoSpec.Translation.ErgoInlineContext.
Require Import ErgoSpec.Translation.ErgoCtoErgoNNRC.
Require Import ErgoSpec.Translation.ErgoNNRCtoJavaScript.
Require Import ErgoSpec.Translation.ErgoNNRCtoJavaScriptCicero.
Require Import ErgoSpec.Translation.ErgoNNRCtoJava.

Section ErgoDriver.

  Section Compiler.
    
    Definition compilation_ctxt : Set := list laergo_module * namespace_ctxt.
    Definition namespace_ctxt_of_compilation_ctxt (ctxt:compilation_ctxt) : namespace_ctxt :=
      snd ctxt.
    Definition modules_of_compilation_ctxt  (ctxt:compilation_ctxt) : list laergo_module :=
      fst ctxt.
    Definition update_namespace_ctxt (ctxt:compilation_ctxt) (ns_ctxt:namespace_ctxt) :=
      (fst ctxt, ns_ctxt).

    Definition set_namespace_in_compilation_ctxt (ctxt:compilation_ctxt) (ns:namespace_name) : compilation_ctxt :=
      update_namespace_ctxt
        ctxt (new_namespace_scope
                (namespace_ctxt_of_compilation_ctxt ctxt)
                ns).

    (* Initialize compilation context *)
    Definition compilation_ctxt_from_inputs
               (ctos:list lrcto_package)
               (mls:list lrergo_module) : eresult compilation_ctxt :=
      let ictos := map InputCTO ctos in
      let imls := map InputErgo mls in
      let ctxt := init_namespace_ctxt in
      resolve_ergo_inputs ctxt (ictos ++ imls).

    Definition ergo_make_stdlib_ctxt
               (ctos:list lrcto_package)
               (mls:list lrergo_module)
      : compilation_ctxt :=
      match (compilation_ctxt_from_inputs ctos mls) with
      | Success _ _ r => r
      | Failure _ _ f => (nil, init_namespace_ctxt)
      end.

    Definition ergo_make_stdlib_namespace
               (ctos:list lrcto_package)
               (mls:list lrergo_module)
      : namespace_ctxt :=
      match (elift namespace_ctxt_of_compilation_ctxt) (compilation_ctxt_from_inputs ctos mls) with
      | Success _ _ r => r
      | Failure _ _ f => init_namespace_ctxt
      end.

    (* Ergo -> ErgoC *)
    Definition ergo_module_to_ergo_calculus
               (ctxt:compilation_ctxt)
               (lm:lrergo_module) : eresult (ergoc_module * compilation_ctxt) :=
      let ns_ctxt := namespace_ctxt_of_compilation_ctxt ctxt in
      let am := resolve_ergo_module ns_ctxt lm in
      eolift (fun amc =>
                let ctxt := update_namespace_ctxt ctxt (snd amc) in
                let p := expand_ergo_module (fst amc) in
                eolift (fun p =>
                          elift
                            (fun pc => (pc, ctxt))
                            (ergo_module_to_calculus p)) p)
             am.

    (* ErgoDecl -> ErgoCDecl *)
    Definition ergo_declaration_to_ergo_calculus
               (ctxt:compilation_ctxt)
               (ld:lrergo_declaration) : eresult (option ergoc_declaration * compilation_ctxt) :=
      let ns_ctxt := namespace_ctxt_of_compilation_ctxt ctxt in
      let am := resolve_ergo_declaration ns_ctxt ld in
      eolift (fun amc =>
                let ctxt := update_namespace_ctxt ctxt (snd amc) in
                elift
                  (fun d => (d, ctxt))
                  (declaration_to_calculus (fst amc)))
             am.

    Definition ergo_declaration_to_ergo_calculus_inlined
               (sctxt : compilation_ctxt)
               (ictxt : inline_context)
               (decl : lrergo_declaration)
      : eresult (option ergoc_declaration * compilation_ctxt * inline_context) :=
      match ergo_declaration_to_ergo_calculus sctxt decl with
      | Failure _ _ f => efailure f
      | Success _ _ (None, sctxt') => esuccess (None, sctxt', ictxt)
      | Success _ _ (Some decl', sctxt') =>
        match ergoc_inline_declaration ictxt decl' with
        | Failure _ _ f => efailure f
        | Success _ _ (ictxt', decl'') => esuccess (Some decl'', sctxt', ictxt')
        end
      end.

    Definition ergo_module_to_javascript
               (ctxt:compilation_ctxt)
               (p:lrergo_module) : eresult ErgoCodeGen.javascript :=
      let rmods := modules_of_compilation_ctxt ctxt in
      let pc := ergo_module_to_ergo_calculus ctxt p in
      let pn := eolift (fun xy => ergoc_module_to_nnrc rmods (fst xy)) pc in
      elift nnrc_module_to_javascript_top pn.

    Definition ergo_module_to_javascript_top
               (ctos:list lrcto_package)
               (mls:list lrergo_module)
               (p:lrergo_module) : eresult ErgoCodeGen.javascript :=
      let ctxt := compilation_ctxt_from_inputs ctos mls in
      eolift (fun ctxt => ergo_module_to_javascript ctxt p) ctxt.
    
    Definition ergo_module_to_java
               (ctxt:compilation_ctxt)
               (p:lrergo_module) : eresult ErgoCodeGen.java :=
      let rmods := modules_of_compilation_ctxt ctxt in
      let pc := ergo_module_to_ergo_calculus ctxt p in
      let pn := eolift (fun xy => ergoc_module_to_nnrc rmods (fst xy)) pc in
      elift nnrc_module_to_java_top pn.

    Definition ergo_module_to_java_top
               (ctos:list lrcto_package)
               (mls:list lrergo_module)
               (p:lrergo_module) : eresult ErgoCodeGen.java :=
      let ctxt := compilation_ctxt_from_inputs ctos mls in
      eolift (fun ctxt => ergo_module_to_java ctxt p) ctxt.

    Definition ergo_module_to_javascript_cicero_top
               (ctos:list cto_package)
               (mls:list lrergo_module)
               (p:ergo_module) : eresult ErgoCodeGen.javascript :=
      let ctxt := init_namespace_ctxt in
      let rctos := resolve_cto_packages ctxt ctos in
      let rmods := eolift (fun rctos => resolve_ergo_modules (snd rctos) mls) rctos in
      let p := eolift (fun pc => resolve_ergo_module (snd pc) p) rmods in
      let p := eolift (fun pc => expand_ergo_module (fst pc)) p in
      let ec := eolift lookup_single_contract p in
      eolift
        (fun c : local_name * ergo_contract =>
           let contract_name := (fst c) in 
           let sigs := lookup_contract_signatures (snd c) in
           let pc := eolift ergo_module_to_calculus p in
           let pn :=
               eolift
                 (fun rmods =>
                    eolift (ergoc_module_to_nnrc (fst rmods)) pc) rmods
           in
           elift (ergoc_module_to_javascript_cicero contract_name (snd c).(contract_state) sigs) pn)
        ec.
  End Compiler.

  Section Interpreter.
    Definition ergo_maybe_update_context
               (ctxt : compilation_ctxt * inline_context * eval_context)
               (result : eresult (compilation_ctxt * inline_context * eval_context * option ergo_data))
    : (compilation_ctxt * inline_context * eval_context) :=
      match result with
      | Success _ _ (sctxt', ictxt', dctxt', _) => (sctxt', ictxt', dctxt')
      | _ => ctxt
      end.

    Definition unpack_output
               (out : ergo_data)
      : option (ergo_data * list ergo_data * ergo_data) :=
      match out with
      | (dleft (drec (("response"%string, response)
                        ::("state"%string, state)
                        ::("emit"%string, dcoll emits)
                        ::nil))) =>
        Some (response, emits, state)
      | _ => None
      end.

    Definition ergo_eval_decl_via_calculus
               (sctxt : compilation_ctxt)
               (ictxt : inline_context)
               (dctxt : eval_context)
               (decl : lrergo_declaration)
    : eresult (compilation_ctxt * inline_context * eval_context * option ergo_data) :=
      match ergo_declaration_to_ergo_calculus_inlined sctxt ictxt decl with
      | Failure _ _ f => efailure f
      | Success _ _ (None, sctxt', ictxt') => esuccess (sctxt', ictxt', dctxt, None)
      | Success _ _ (Some decl', sctxt', ictxt') =>
        match ergoc_eval_decl dctxt decl' with
        | Failure _ _ f => efailure f
        | Success _ _ (dctxt', None) => esuccess (sctxt', ictxt', dctxt', None)
        | Success _ _ (dctxt', Some out) =>
          match unpack_output out with
          | None => esuccess (sctxt', ictxt', dctxt', Some out)
          | Some (_, _, state) =>
            esuccess (
                sctxt',
                ictxt',
                eval_context_update_local_env dctxt' "state"%string state,
                Some out
              )
          end
        end
      end.

    Definition string_of_response (response : ergo_data) : string :=
      (fmt_grn "Response. ") ++ (ErgoData.data_to_json_string fmt_dq response) ++ fmt_nl.

    Definition string_of_emits (emits : list ergo_data) : string :=
      (fold_left
         (fun old new => ((fmt_mag "Emit. ") ++ new ++ fmt_nl ++ old)%string)
         (map (ErgoData.data_to_json_string fmt_dq) emits) ""%string).

    Definition string_of_state (ctxt : eval_context) (state : ergo_data)
    : string :=
      let jsonify := ErgoData.data_to_json_string fmt_dq in
      let old_st := lookup String.string_dec (ctxt.(eval_context_local_env)) "state"%string in
      let new_st := state in
      match old_st with
      | None => (fmt_blu "State. ") ++ (jsonify state)
      | Some state' =>
        if Data.data_eq_dec state state' then
          ""%string
        else
          (fmt_blu "State. ") ++ (jsonify state) ++ fmt_nl
      end.

    (* XXX May be nice to replace by a format that aligns with Ergo notations instead of JSON and move to an earlier module e.g., Common/Utils/EData *)
    Definition string_of_result (ctxt : eval_context) (result : option ergo_data)
      : string :=
      match result with
      | None => ""
      | Some (dright msg) =>
        fmt_red ("Error. "%string) ++ (ErgoData.data_to_json_string fmt_dq msg) ++ fmt_nl
      | Some out =>
        match unpack_output out with
        | Some (response, emits, state) =>
            (string_of_emits emits) ++ (string_of_response response) ++ (string_of_state ctxt state)
        | None => (ErgoData.data_to_json_string fmt_dq out) ++ fmt_nl
        end
(* Note: this was previously powered by QCert's dataToString d, and I kind of
   liked that better anyway, so we might transition back at some point. The
   problem was that QCert treated arrays as bags and sorted them before
   printing (!!!). *)
      end.

    Definition ergo_string_of_result
               (ctxt : eval_context)
               (result : eresult (compilation_ctxt * inline_context * eval_context * option ergo_data))
      : string :=
      elift_both
        (string_of_result ctxt)
        (fun e => string_of_error e ++ fmt_nl)%string
        (elift (fun x => match x with | (_, _, y) => y end) result).

  End Interpreter.

End ErgoDriver.

