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
Require Import ErgoSpec.Common.Utils.EUtil.
Require Import ErgoSpec.Common.Utils.ENames.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Utils.EData.
Require Import ErgoSpec.Common.Utils.EAstUtil.
Require Import ErgoSpec.Common.CTO.CTO.
Require Import ErgoSpec.Common.Types.ErgoType.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.Ergo.Lang.ErgoExpand.
Require Import ErgoSpec.ErgoC.Lang.ErgoC.
Require Import ErgoSpec.ErgoC.Lang.ErgoCTypeContext.
Require Import ErgoSpec.ErgoC.Lang.ErgoCType.
Require Import ErgoSpec.ErgoC.Lang.ErgoCEvalContext.
Require Import ErgoSpec.ErgoC.Lang.ErgoCEval.
Require Import ErgoSpec.Translation.CTOtoErgo.
Require Import ErgoSpec.Translation.ErgoNameResolve.
Require Import ErgoSpec.Translation.ErgotoErgoC.
Require Import ErgoSpec.Translation.ErgoCompContext.
Require Import ErgoSpec.Translation.ErgoCInline.
Require Import ErgoSpec.Translation.ErgoCtoErgoNNRC.
Require Import ErgoSpec.Translation.ErgoNNRCtoJavaScript.
Require Import ErgoSpec.Translation.ErgoNNRCtoJavaScriptCicero.
Require Import ErgoSpec.Translation.ErgoNNRCtoJava.

Section ErgoDriver.

  Section Compiler.
    (* Ergo -> ErgoC *)
    Definition ergo_module_to_ergoc
               (ctxt:compilation_context)
               (lm:lrergo_module) : eresult (ergoc_module * compilation_context) :=
      let ns_ctxt := namespace_ctxt_of_compilation_context ctxt in
      let am := resolve_ergo_module ns_ctxt lm in
      eolift (fun amc =>
                let ctxt := compilation_context_update_namespace ctxt (snd amc) in
                let p := expand_ergo_module (fst amc) in
                let pc := eolift (ergo_module_to_calculus ctxt) p in
                eolift (fun xy => ergoc_inline_module (snd xy) (fst xy)) pc)
             am.

    Definition ergo_modules_to_ergoc
               (ctxt:compilation_context)
               (lm:list lrergo_module) : eresult (list ergoc_module * compilation_context) :=
      elift_context_fold_left
        ergo_module_to_ergoc
        lm
        ctxt.

    (* Initialize compilation context *)
    Definition compilation_context_from_ctos
               (ctos:list lrcto_package) : eresult compilation_context :=
      let ctxt := init_namespace_ctxt in
      elift (fun resolved_mods : list laergo_module * namespace_ctxt =>
               let (_,ns_ctxt) := resolved_mods in
               init_compilation_context ns_ctxt)
            (resolve_cto_packages ctxt ctos).

    Definition compilation_context_from_inputs
               (ctos:list lrcto_package)
               (mls:list lrergo_module) : eresult compilation_context :=
      let rctxt := compilation_context_from_ctos ctos in
      eolift (fun ctxt => elift snd (ergo_modules_to_ergoc ctxt mls)) rctxt.

    (* ErgoDecl -> ErgoCDecl *)
    Definition ergo_declaration_to_ergoc
               (ctxt:compilation_context)
               (ld:lrergo_declaration) : eresult (list ergoc_declaration * compilation_context) :=
      let ns_ctxt := namespace_ctxt_of_compilation_context ctxt in
      let am := resolve_ergo_declaration ns_ctxt ld in
      eolift (fun amc =>
                let ctxt := compilation_context_update_namespace ctxt (snd amc) in
                declaration_to_calculus ctxt (fst amc))
             am.

    Definition ergo_declaration_to_ergoc_inlined
               (sctxt : compilation_context)
               (decl : lrergo_declaration)
      : eresult (list ergoc_declaration * compilation_context) :=
      eolift
        (fun (x : list ergoc_declaration * compilation_context) =>
           let (decls, ctxt) := x in
           elift_context_fold_left
             ergoc_inline_declaration
             decls
             ctxt)
        (ergo_declaration_to_ergoc sctxt decl).

    Definition ergo_module_to_javascript
               (ctxt:compilation_context)
               (p:lrergo_module) : eresult ErgoCodeGen.javascript :=
      let pc := ergo_module_to_ergoc ctxt p in
      let pn := eolift (fun xy => ergoc_module_to_nnrc (fst xy)) pc in
      elift nnrc_module_to_javascript_top pn.

    Definition ergo_module_to_javascript_top
               (ctos:list lrcto_package)
               (mls:list lrergo_module)
               (p:lrergo_module) : eresult ErgoCodeGen.javascript :=
      let ctxt := compilation_context_from_inputs ctos mls in
      eolift (fun ctxt => ergo_module_to_javascript ctxt p) ctxt.

    Definition ergo_module_to_java
               (ctxt:compilation_context)
               (p:lrergo_module) : eresult ErgoCodeGen.java :=
      let pc := ergo_module_to_ergoc ctxt p in
      let pn := eolift (fun xy => ergoc_module_to_nnrc (fst xy)) pc in
      elift nnrc_module_to_java_top pn.

    Definition ergo_module_to_java_top
               (ctos:list lrcto_package)
               (mls:list lrergo_module)
               (p:lrergo_module) : eresult ErgoCodeGen.java :=
      let ctxt := compilation_context_from_inputs ctos mls in
      eolift (fun ctxt => ergo_module_to_java ctxt p) ctxt.

    Definition ergo_module_to_javascript_cicero_top
               (ctos:list cto_package)
               (mls:list lrergo_module)
               (p:lrergo_module) : eresult ErgoCodeGen.javascript :=
      let ctxt := compilation_context_from_inputs ctos mls in
      let p :=
          eolift (fun am =>
                    let ns_ctxt := namespace_ctxt_of_compilation_context am in
                    resolve_ergo_module ns_ctxt p) ctxt
      in
      eolift
        (fun p =>
           let ctxt :=
               elift (fun ct => compilation_context_update_namespace ct (snd p)) ctxt
           in
           let p := expand_ergo_module (fst p) in
           let ec := eolift lookup_single_contract p in
           eolift
             (fun c : local_name * ergo_contract =>
                let contract_name := (fst c) in 
                let sigs := lookup_contract_signatures (snd c) in
                let pc :=
                    eolift (fun ct =>
                              eolift (fun p => ergoc_inline_module (snd p) (fst p))
                                     (eolift (ergo_module_to_calculus ct) p)) ctxt
                in
                let pn := eolift (fun xy => ergoc_module_to_nnrc (fst xy)) pc in
                elift (ergoc_module_to_javascript_cicero contract_name (snd c).(contract_state) sigs) pn)
             ec)
        p.

  End Compiler.

  Section Interpreter.
    Context {m:brand_model}.

    (*
    Definition test_brand_model := (ErgoCTypes.empty_brand_model tt eq_refl).
    Definition test_brand_relation := mkBrand_relation nil (eq_refl _) (eq_reflexivity _).
*)
    Record repl_context :=
      mkREPLCtxt {
          repl_context_type_ctxt : type_context;
          repl_context_eval_ctxt : eval_context;
          repl_context_comp_ctxt : compilation_context
        }.

    Definition init_repl_context
               (ctos : list lrcto_package)
               (mls : list lrergo_module) : eresult repl_context :=
      elift (mkREPLCtxt ErgoCTypeContext.empty_type_context ErgoCEvalContext.empty_eval_context)
            (eolift (set_namespace_in_compilation_context
                       "org.accordproject.ergotop"%string)
                    (compilation_context_from_inputs ctos mls)).

    Definition update_repl_ctxt_comp_ctxt
               (rctxt: repl_context)
               (sctxt: compilation_context) : repl_context :=
      mkREPLCtxt rctxt.(repl_context_type_ctxt) rctxt.(repl_context_eval_ctxt) sctxt.
    
    Definition update_repl_ctxt_type_ctxt
               (rctxt: repl_context)
               (nctxt: type_context) : repl_context :=
      mkREPLCtxt nctxt rctxt.(repl_context_eval_ctxt) rctxt.(repl_context_comp_ctxt).
    
    Definition update_repl_ctxt_eval_ctxt
               (rctxt: repl_context)
               (nctxt: eval_context) : repl_context :=
      mkREPLCtxt rctxt.(repl_context_type_ctxt) nctxt rctxt.(repl_context_comp_ctxt).
    
    Definition lift_repl_ctxt
               (orig_ctxt : repl_context)
               (result : eresult (option ergoc_type * option ergo_data * repl_context))
               : repl_context
      :=
        elift_both
          (fun s => snd s) (* in case of success, second part of result is the new context *)
          (fun e => orig_ctxt)  (* in case of failure, ignore the failure and return the original context *)
          result.

    Definition ergoc_repl_eval_declaration
               (ctxt:repl_context) (decl:ergoc_declaration)
      : eresult (option ergoc_type * option ergo_data * repl_context) :=
      let sctxt := ctxt.(repl_context_comp_ctxt) in
      match ergoc_type_decl ctxt.(repl_context_type_ctxt) decl with
      | Failure _ _ f => efailure f
      | Success _ _ (tctxt', typ) =>
        match ergoc_eval_decl ctxt.(repl_context_eval_ctxt) decl with
        | Failure _ _ f => efailure f
        | Success _ _ (dctxt', None) => esuccess (typ, None, mkREPLCtxt tctxt' dctxt' sctxt)
        | Success _ _ (dctxt', Some out) =>
          match unpack_output out with
          | None => esuccess (typ, Some out, mkREPLCtxt tctxt' dctxt' sctxt)
          | Some (_, _, state) =>
            esuccess (
                typ,
                Some out,
                mkREPLCtxt
                  tctxt' (* TODO *)
                  (eval_context_update_local_env dctxt' "state"%string state)
                  sctxt
              )
          end
        end
      end.

    Definition ergoc_repl_eval_declarations
               (ctxt:repl_context) (decls:list ergoc_declaration)
      : eresult (option ergoc_type * option ergo_data * repl_context) :=
      elift
        (fun xy =>
           (last_some_pair (fst xy), snd xy))
        (elift_context_fold_left
           ergoc_repl_eval_declaration
           decls
           ctxt).

    Definition ergo_eval_decl_via_calculus
               (ctxt : repl_context)
               (decl : lrergo_declaration)
      : eresult (option ergoc_type * option ergo_data * repl_context) :=
      match ergo_declaration_to_ergoc_inlined ctxt.(repl_context_comp_ctxt) decl with
      | Failure _ _ f => efailure f
      | Success _ _ (decls, sctxt') =>
        let rctxt' := update_repl_ctxt_comp_ctxt ctxt sctxt' in
        ergoc_repl_eval_declarations rctxt' decls
      end.

    Definition ergo_string_of_result
               (rctxt : repl_context)
               (result : eresult (option ergoc_type * option ergo_data * repl_context))
      : eresult string :=
      let local_env := rctxt.(repl_context_eval_ctxt).(eval_context_local_env) in
      let old_state := lookup String.string_dec local_env "state"%string in
      elift
        (string_of_result old_state)
        (elift fst result).

    Definition ergo_repl_eval_decl
               (rctxt : repl_context)
               (decl : lrergo_declaration)
      : eresult string * repl_context :=
      let result := ergo_eval_decl_via_calculus rctxt decl in
      let out := ergo_string_of_result rctxt result in
      (out, lift_repl_ctxt rctxt result).

  End Interpreter.

End ErgoDriver.

