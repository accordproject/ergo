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
Require Import ErgoSpec.Common.Utils.EProvenance.
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
  Section CompilerPre.
    Definition resolve_inputs
               (inputs:list lrergo_input) : eresult ((list laergo_module * laergo_module) * namespace_ctxt) :=
      let '(ctos, mls, p) := split_ctos_and_ergos inputs in
      match p with
      | Some p =>
        let ctxt := init_namespace_ctxt in
        let rctxt := resolve_cto_packages ctxt ctos in
        let mls :=
            eolift (fun ctxt =>
                      elift
                        (fun res =>
                           (fst ctxt ++ fst res, snd res))
                        (resolve_ergo_modules (snd ctxt) mls))
                   rctxt
        in
        eolift (fun ctxt =>
                  elift (fun rp =>
                           ((fst ctxt, (fst rp)), snd rp))
                        (resolve_ergo_module (snd ctxt) p)
               ) mls
      | None => no_ergo_module_error dummy_provenance
      end.

    Definition just_resolved_inputs
               (inputs:list lrergo_input) : eresult (list laergo_module) :=
      let resolved := resolve_inputs inputs in
      elift (fun x => (fst (fst x)) ++ ((snd (fst x))::nil)) resolved.

    Definition brand_model_from_inputs (inputs : list lrergo_input) : eresult ErgoCTypes.tbrand_model :=
      let resolved := just_resolved_inputs inputs in
      let type_decls := elift modules_get_type_decls resolved in
      eolift ErgoTypetoErgoCType.brand_model_of_declarations type_decls.

  End CompilerPre.

  Section CompilerCore.
    Context {bm:brand_model}.

    (* Initialize compilation context *)
    Definition init_compilation_context_from_inputs
               (inputs:list lrergo_input) :
      eresult ((list laergo_module * laergo_module) * compilation_context) :=
      let rinputs := resolve_inputs inputs in
      elift
        (fun rinputs =>
           let '(mls, p, ns_ctxt) := rinputs in
           (mls, p, init_compilation_context ns_ctxt))
        rinputs.

    (* Ergo -> ErgoC *)
    Definition ergo_module_to_ergoc
               (ctxt:compilation_context)
               (lm:laergo_module) : eresult (ergoc_module * compilation_context) :=
      let p := expand_ergo_module lm in
      let pc := eolift (ergo_module_to_calculus ctxt) p in
      eolift (fun xy => ergoc_inline_module (snd xy) (fst xy)) pc.

    Definition ergo_modules_to_ergoc
               (ctxt:compilation_context)
               (lm:list laergo_module) : eresult (list ergoc_module * compilation_context) :=
      elift_context_fold_left
        ergo_module_to_ergoc
        lm
        ctxt.

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
      : eresult (list (option ergoc_type * ergoc_declaration) * compilation_context) :=
      (* Translation *)
      let ec := ergo_declaration_to_ergoc sctxt decl in
      (* Inlining *)
      let inlined : eresult (list ergoc_declaration * compilation_context) :=
          eolift
            (fun (x : list ergoc_declaration * compilation_context) =>
               let (decls, ctxt) := x in
               elift_context_fold_left
                 ergoc_inline_declaration
                 decls
                 ctxt)
            ec
      in
      (* Type-checking *)
      eolift (fun xy : list ergoc_declaration * compilation_context =>
                elift_context_fold_left
                  (fun (sctxt : compilation_context) (decl : ergoc_declaration) =>
                     match ergoc_type_decl sctxt.(compilation_context_type_ctxt) decl with
                     | Failure _ _ f => efailure f
                     | Success _ _ (tctxt', typ) =>
                       esuccess ((typ,decl), compilation_context_update_type_ctxt sctxt tctxt')
                     end)
                  (fst xy)
                  (snd xy)
             ) inlined.
        
    Definition ergo_module_to_javascript
               (ctxt:compilation_context)
               (p:laergo_module) : eresult ErgoCodeGen.javascript :=
      let pc := ergo_module_to_ergoc ctxt p in
      let pn := eolift (fun xy => ergoc_module_to_nnrc (fst xy)) pc in
      elift nnrc_module_to_javascript_top pn.

    Definition compilation_context_from_most_inputs
               (inputs:list lrergo_input) : eresult (laergo_module * compilation_context) :=
      let cinit := init_compilation_context_from_inputs inputs in
      eolift (fun init =>
                let '(mls, p, ctxt) := init in
                elift (fun r => (p, snd r))
                      (ergo_modules_to_ergoc ctxt mls))
             cinit.
    
    Definition compilation_context_from_inputs
               (inputs:list lrergo_input) : eresult compilation_context :=
      let cinit := init_compilation_context_from_inputs inputs in
      eolift (fun init =>
                let '(mls, p, ctxt) := init in
                elift snd
                      (ergo_modules_to_ergoc ctxt (mls ++ (p::nil))))
             cinit.
    
    Definition ergo_module_to_java
               (ctxt:compilation_context)
               (p:laergo_module) : eresult ErgoCodeGen.java :=
      let pc := ergo_module_to_ergoc ctxt p in
      let pn := eolift (fun xy => ergoc_module_to_nnrc (fst xy)) pc in
      elift nnrc_module_to_java_top pn.

  End CompilerCore.

  Section CompilerTop.

    Definition ergo_module_to_javascript_top
               (inputs:list lrergo_input) : eresult result_file :=
      let bm : eresult brand_model := brand_model_from_inputs inputs in
      eolift (fun bm :brand_model=>
                let cinit := compilation_context_from_most_inputs inputs in
                eolift (fun init : laergo_module * compilation_context =>
                          let (p, ctxt) := init in
                          let res := ergo_module_to_javascript ctxt p in
                          elift (mkResultFile p.(module_file)) res)
                       cinit) bm.

    Definition ergo_module_to_java_top
               (inputs:list lrergo_input) : eresult result_file :=
      let bm : eresult brand_model := brand_model_from_inputs inputs in
      eolift (fun bm :brand_model=>
                let cinit := compilation_context_from_most_inputs inputs in
                eolift (fun init : laergo_module * compilation_context =>
                          let (p, ctxt) := init in
                          let res := ergo_module_to_java ctxt p in
                          elift (mkResultFile p.(module_file)) res)
                       cinit) bm.

    Definition ergo_module_to_javascript_cicero_top
               (inputs:list lrergo_input) : eresult result_file :=
      let bm : eresult brand_model := brand_model_from_inputs inputs in
      eolift
        (fun bm : brand_model=>
           let ctxt := compilation_context_from_most_inputs inputs in
           eolift
             (fun init : laergo_module * compilation_context =>
                let (p, ctxt) := init in
                let res :=
                    let ec := lookup_single_contract p in
                    eolift
                      (fun c : local_name * ergo_contract =>
                         let contract_name := (fst c) in 
                         let sigs := lookup_contract_signatures (snd c) in
                         let pc := ergo_module_to_ergoc ctxt p in
                         let pn := eolift (fun xy => ergoc_module_to_nnrc (fst xy)) pc in
                         elift (ergoc_module_to_javascript_cicero contract_name (snd c).(contract_state) sigs) pn)
                      ec
                in
                elift (mkResultFile p.(module_file)) res)
             ctxt) bm.
    
  End CompilerTop.

  Section Interpreter.
    Context {bm:brand_model}.

    Record repl_context :=
      mkREPLCtxt {
          repl_context_eval_ctxt : eval_context;
          repl_context_comp_ctxt : compilation_context;
        }.

    Definition init_repl_context
               (inputs : list lrergo_input) : eresult repl_context :=
      elift (mkREPLCtxt ErgoCEvalContext.empty_eval_context)
            (eolift (set_namespace_in_compilation_context
                       "org.accordproject.ergotop"%string)
                    (compilation_context_from_inputs inputs)).

    Definition update_repl_ctxt_comp_ctxt
               (rctxt: repl_context)
               (sctxt: compilation_context) : repl_context :=
      mkREPLCtxt
        rctxt.(repl_context_eval_ctxt)
        sctxt.
    
    Definition update_repl_ctxt_type_ctxt
               (rctxt: repl_context)
               (nctxt: type_context) : repl_context :=
      update_repl_ctxt_comp_ctxt
        rctxt
        (compilation_context_update_type_ctxt rctxt.(repl_context_comp_ctxt) nctxt).
    
    Definition update_repl_ctxt_eval_ctxt
               (rctxt: repl_context)
               (nctxt: eval_context) : repl_context :=
      mkREPLCtxt
        nctxt
        rctxt.(repl_context_comp_ctxt).

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
               (ctxt:repl_context) (typed_decl:option ergoc_type * ergoc_declaration)
      : eresult (option ergoc_type * option ergo_data * repl_context) :=
      let (typ, decl) := typed_decl in
      match ergoc_eval_decl ctxt.(repl_context_eval_ctxt) decl with
      | Failure _ _ f => efailure f
      | Success _ _ (dctxt', None) => esuccess (typ, None, update_repl_ctxt_eval_ctxt ctxt dctxt')
      | Success _ _ (dctxt', Some out) =>
        match unpack_output out with
        | None => esuccess (typ, Some out, update_repl_ctxt_eval_ctxt ctxt dctxt')
        | Some (_, _, state) =>
          esuccess (
              typ,
              Some out,
              update_repl_ctxt_eval_ctxt ctxt (eval_context_update_local_env dctxt' "state"%string state)
            )
        end
      end.

    Definition ergoc_repl_eval_declarations
               (ctxt:repl_context) (decls:list (option ergoc_type * ergoc_declaration))
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

