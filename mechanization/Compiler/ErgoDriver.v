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

Require Import ErgoSpec.Utils.Misc.
Require Import ErgoSpec.Backend.ForeignErgo.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.NamespaceContext.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.Ast.
Require Import ErgoSpec.Common.PrintTypedData.
Require Import ErgoSpec.Types.CTO.
Require Import ErgoSpec.Types.ErgoType.
Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import ErgoSpec.ErgoC.Lang.ErgoC.
Require Import ErgoSpec.ErgoC.Lang.ErgoCEvalContext.
Require Import ErgoSpec.ErgoC.Lang.ErgoCEval.
Require Import ErgoSpec.ErgoC.Lang.ErgoCT.
Require Import ErgoSpec.ErgoC.Lang.ErgoCTypecheckContext.
Require Import ErgoSpec.ErgoC.Lang.ErgoCTypecheck.
Require Import ErgoSpec.ErgoC.Lang.ErgoCExpand.
Require Import ErgoSpec.ErgoNNRC.Lang.ErgoNNRC.
Require Import ErgoSpec.Translation.CTOtoErgo.
Require Import ErgoSpec.Translation.ErgoNameResolve.
Require Import ErgoSpec.Translation.ErgotoErgoC.
Require Import ErgoSpec.Translation.ErgoCompContext.
Require Import ErgoSpec.Translation.ErgoCInline.
Require Import ErgoSpec.Translation.ErgoCTtoErgoNNRC.
Require Import ErgoSpec.Translation.ErgoNNRCtoJavaScript.
Require Import ErgoSpec.Translation.ErgoNNRCtoCicero.
Require Import ErgoSpec.Translation.ErgoNNRCtoJava.

Section ErgoDriver.
  Section CompilerPre.
    Definition resolve_inputs_opt
               (inputs:list lrergo_input)
    : eresult ((list laergo_module * option laergo_module) * namespace_ctxt) :=
      let '(ctos, mls, p) := split_ctos_and_ergos inputs in
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
      match p with
      | Some p =>
        eolift (fun ctxt =>
                  elift (fun rp =>
                           ((fst ctxt, Some (fst rp)), snd rp))
                        (resolve_ergo_module (snd ctxt) p)
               ) mls
      | None =>
        elift (fun ctxt => ((fst ctxt, None), (snd ctxt))) mls
      end.

    Definition resolve_inputs
               (inputs:list lrergo_input)
      : eresult ((list laergo_module * laergo_module) * namespace_ctxt) :=
      eolift (fun res =>
                let '(mls, op, ctxt) := res in
                match op with
                | Some p => esuccess (mls, p, ctxt) nil
                | None => no_ergo_module_error dummy_provenance
                end) (resolve_inputs_opt inputs).

    Definition resolve_inputs_no_main
               (inputs:list lrergo_input)
      : eresult (list laergo_module * namespace_ctxt) :=
      elift (fun res =>
               let '(mls, op, ctxt) := res in
               match op with
               | Some p => (mls ++ (p::nil), ctxt)
               | None => (mls, ctxt)
               end) (resolve_inputs_opt inputs).
      
    Definition just_resolved_inputs
               (inputs:list lrergo_input) : eresult (list laergo_module) :=
      let resolved := resolve_inputs_no_main inputs in
      elift (fun x => (fst x)) resolved.

    Definition brand_model_from_inputs (inputs : list lrergo_input) : eresult (ErgoCType.tbrand_model * list laergo_type_declaration) :=
      let resolved := just_resolved_inputs inputs in
      let type_decls := elift modules_get_type_decls resolved in
      eolift ErgoTypetoErgoCType.brand_model_of_declarations type_decls.

  End CompilerPre.

  Section CompilerCore.
    Context {bm:brand_model}.

    (* Initialize compilation context *)
    Definition init_compilation_context_from_inputs
               (inputs:list lrergo_input)
               (order:list laergo_type_declaration) :
      eresult ((list laergo_module * laergo_module) * compilation_context) :=
      let rinputs := resolve_inputs inputs in
      elift
        (fun rinputs =>
           let '(mls, p, ns_ctxt) := rinputs in
           (mls, p, init_compilation_context ns_ctxt order))
        rinputs.

    Definition init_compilation_context_from_inputs_no_main
               (inputs:list lrergo_input)
               (order:list laergo_type_declaration) :
      eresult (list laergo_module * compilation_context) :=
      let rinputs := resolve_inputs_no_main inputs in
      elift
        (fun rinputs =>
           let '(mls, ns_ctxt) := rinputs in
           (mls, init_compilation_context ns_ctxt order))
        rinputs.

    (* Ergo -> ErgoC *)
    Definition ergo_module_to_ergoct
               (ctxt:compilation_context)
               (lm:laergo_module) : eresult (ergoct_module * compilation_context) :=
      let pc := ergo_module_to_calculus ctxt lm in
      let pc := eolift (fun xy =>
                          let c := snd xy in
                          let order := get_all_decls c in
                          elift (fun x => (x,c))
                                (ergoc_expand_module order (fst xy))) pc in
      let pc := eolift (fun xy => ergoc_inline_module (snd xy) (fst xy)) pc in
      eolift (fun xy : ergoc_module * compilation_context =>
                let (mod,ctxt) := xy in
                let nsctxt := ctxt.(compilation_context_namespace) in
                let sctxt := ctxt.(compilation_context_type_ctxt) in
                let pctypes := ergoc_typecheck_module nsctxt sctxt mod in
                elift (fun xy : ergoct_module * type_context =>
                         let (mod, sctxt') := xy in
                         (mod, compilation_context_update_type_ctxt ctxt sctxt')) pctypes
             ) pc.

    Definition ergo_modules_to_ergoct
               (ctxt:compilation_context)
               (lm:list laergo_module) : eresult (list ergoct_module * compilation_context) :=
      coq_time "ergo->ergoc(typed)"
               (elift_context_fold_left
                  ergo_module_to_ergoct
                  lm)
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

    Definition ergo_declaration_to_ergoct_inlined
               (sctxt : compilation_context)
               (decl : lrergo_declaration)
      : eresult (list ergoct_declaration * compilation_context) :=
      (* Translation *)
      let ec := ergo_declaration_to_ergoc sctxt decl in
      let ec := eolift (fun xy =>
                          let c := snd xy in
                          let order := get_all_decls c in
                          elift (fun x => (x, c))
                                (ergoc_expand_declarations order (fst xy)))
                       ec in
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
                     let nsctxt := sctxt.(compilation_context_namespace)  in
                     elift (fun xy : ergoct_declaration * type_context =>
                              let (declt, tctxt') := xy in
                              (declt, compilation_context_update_type_ctxt sctxt tctxt'))
                           (ergoc_typecheck_decl nsctxt sctxt.(compilation_context_type_ctxt) decl)
)
                  (fst xy)
                  (snd xy)
             ) inlined.

    Definition ergo_module_to_javascript
               (version:jsversion)
               (ctxt:compilation_context)
               (p:laergo_module) : eresult (nnrc_module * ErgoCodeGen.ejavascript) :=
      let pc := ergo_module_to_ergoct ctxt p in
      let pn :=
          coq_time "ergoc(typed)->nnrc"
                   (eolift (fun xy => ergoct_module_to_nnrc (fst xy))) pc in
      coq_time "nnrc->js"
               (elift (fun x => (x,nnrc_module_to_javascript_top version (@brand_relation_brands (@brand_model_relation _ bm)) x)))
               pn.

    Definition compilation_context_from_inputs
               (inputs:list lrergo_input)
               (order:list laergo_type_declaration) : eresult (laergo_module * compilation_context) :=
      let cinit := init_compilation_context_from_inputs inputs order in
      eolift (fun init =>
                let '(mls, p, ctxt) := init in
                elift (fun r => (p, snd r))
                      (ergo_modules_to_ergoct ctxt mls))
             cinit.
    
    Definition compilation_context_from_inputs_no_main
               (inputs:list lrergo_input)
               (order:list laergo_type_declaration) : eresult compilation_context :=
      let cinit := init_compilation_context_from_inputs_no_main inputs order in
      coq_time "init(load modules)"
               (eolift (fun init =>
                          let '(mls, ctxt) := init in
                          elift snd
                                (ergo_modules_to_ergoct ctxt mls)))
               cinit.
    
    Definition ergo_module_to_java
               (ctxt:compilation_context)
               (p:laergo_module) : eresult (nnrc_module * ErgoCodeGen.java) :=
      let filename := p.(module_prefix) in
      let pc := ergo_module_to_ergoct ctxt p in
      let pn := eolift (fun xy => ergoct_module_to_nnrc (fst xy)) pc in
      elift (fun x => (x, nnrc_module_to_java_top filename x)) pn.

  End CompilerCore.

  Section CompilerTop.

    Local Open Scope estring_scope.

    Definition ergo_module_to_javascript_top
               (version:jsversion)
               (inputs:list lrergo_input) : eresult result_file :=
      let bm : eresult (brand_model * list laergo_type_declaration) :=
          coq_time "init(load types)"
                   brand_model_from_inputs inputs in
      eolift (fun xy :brand_model * list laergo_type_declaration=>
                let bm := fst xy in
                let cinit := compilation_context_from_inputs inputs (snd xy) in
                eolift (fun init : laergo_module * compilation_context =>
                          let (p, ctxt) := init in
                          let res := ergo_module_to_javascript version ctxt p in
                          elift (fun xy => mkResultFile None p.(module_file) (fst xy) (snd xy)) res)
                       cinit) bm.

    Definition ergo_module_to_java_top
               (inputs:list lrergo_input) : eresult result_file :=
      let bm : eresult (brand_model * list laergo_type_declaration) := brand_model_from_inputs inputs in
      eolift (fun xy :brand_model * list laergo_type_declaration=>
                let bm := fst xy in
                let cinit := compilation_context_from_inputs inputs (snd xy) in
                eolift (fun init : laergo_module * compilation_context =>
                          let (p, ctxt) := init in
                          let res := ergo_module_to_java ctxt p in
                          elift (fun xy => mkResultFile None p.(module_file) (fst xy) (string_to_estring (snd xy))) res)
                       cinit) bm.

    Definition ergo_module_to_cicero_top
               (inputs:list lrergo_input) : eresult result_file :=
      let bm : eresult (brand_model * list laergo_type_declaration) := brand_model_from_inputs inputs in
      eolift
        (fun xy :brand_model * list laergo_type_declaration=>
           let bm := fst xy in
           let ctxt := compilation_context_from_inputs inputs (snd xy) in
           eolift
             (fun init : laergo_module * compilation_context =>
                let (p, ctxt) := init in
                let res :=
                    let ec := lookup_single_contract p in
                    eolift
                      (fun c : local_name * ergo_contract =>
                         let contract_name := (fst c) in 
                         let sigs := lookup_contract_signatures (snd c) in
                         let pc := ergo_module_to_ergoct ctxt p in
                         let pn := eolift (fun xy => ergoct_module_to_nnrc (fst xy)) pc in
                         elift (fun x => (contract_name, x,ergoc_module_to_cicero contract_name (snd c).(contract_state) sigs x)) pn)
                      ec
                in
                elift (fun xyz =>
                         let '(contract_name, nmod, ncontent) := xyz in
                         mkResultFile (Some contract_name) p.(module_file) nmod ncontent)
                      res)
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
            (eolift (set_namespace_in_compilation_context accordproject_ergotop_namespace)
                    (compilation_context_from_inputs_no_main inputs nil)).

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
               (ctxt:repl_context) (decl:ergoct_declaration)
      : eresult (option ergoc_type * option ergo_data * repl_context) :=
      let nsctxt := ctxt.(repl_context_comp_ctxt).(compilation_context_namespace)  in
      let typ := ergoct_declaration_type decl in
      let warnings := ctxt.(repl_context_comp_ctxt).(compilation_context_warnings) in
      let init := eolift (ergoct_eval_decl ctxt.(repl_context_eval_ctxt)) (esuccess decl warnings) in
      eolift (fun xy : eval_context * option ergo_data =>
                let (dctxt', od) := xy in
                match od with
                | None =>
                  esuccess (typ, None, update_repl_ctxt_eval_ctxt ctxt dctxt') nil
                | Some out =>
                  match unpack_output out with
                  | None => esuccess (typ, Some out, update_repl_ctxt_eval_ctxt ctxt dctxt') nil
                  | Some (_, _, state) =>
                    let newctxt :=
                        match typ with (* XXX If we have a data, don't we also have a type ??? *)
                        | None =>
                          esuccess
                            (update_repl_ctxt_eval_ctxt ctxt (eval_context_update_global_env dctxt' this_state state))
                            warnings
                        | Some typ =>
                          elift
                            (fun ty =>
                               let '(_, _, statety) := ty in
                               let ctxt1 :=
                                   update_repl_ctxt_eval_ctxt ctxt (eval_context_update_global_env dctxt' this_state state)
                               in
                               let sctxt1 := ctxt1.(repl_context_comp_ctxt).(compilation_context_type_ctxt) in
                               update_repl_ctxt_type_ctxt ctxt1 (type_context_update_global_env sctxt1 this_state statety))
                            (unpack_success_type nsctxt typ warnings)
                        end
                    in
                    elift (fun ctxt => (typ, Some out, ctxt)) newctxt
                  end
                end) init.

    Definition ergoct_repl_eval_declarations
               (ctxt:repl_context) (decls:list ergoct_declaration)
      : eresult (option ergoc_type * option ergo_data * repl_context) :=
      elift
        (fun xy =>
           (last_some_pair (fst xy), snd xy))
        (elift_context_fold_left
           ergoc_repl_eval_declaration
           decls
           ctxt).

    Definition ergoct_eval_decl_via_calculus
               (ctxt : repl_context)
               (decl : lrergo_declaration)
      : eresult (option ergoc_type * option ergo_data * repl_context) :=
      eolift_warning
        (fun xyw : (list ergoct_declaration * compilation_context) * list ewarning =>
           let '(decls, sctxt', warnings) := xyw in
           let sctxt' := compilation_context_add_warnings sctxt' warnings in
           let rctxt' := update_repl_ctxt_comp_ctxt ctxt sctxt' in
           ergoct_repl_eval_declarations rctxt' decls)
        (ergo_declaration_to_ergoct_inlined ctxt.(repl_context_comp_ctxt) decl).

    Definition ergo_string_of_result
               (rctxt : repl_context)
               (result : eresult (option ergoc_type * option ergo_data * repl_context))
      : eresult string :=
      let nsctxt := rctxt.(repl_context_comp_ctxt).(compilation_context_namespace)  in
      let global_env := rctxt.(repl_context_eval_ctxt).(eval_context_global_env) in
      let old_state := lookup String.string_dec global_env this_state in
      elift
        (string_of_typed_result nsctxt old_state)
        (elift fst result).

    Definition ergoct_repl_eval_decl
               (rctxt : repl_context)
               (decl : lrergo_declaration)
      : eresult string * repl_context :=
      let rctxt :=
          let sctxt := rctxt.(repl_context_comp_ctxt) in
          let sctxt := compilation_context_reset_warnings sctxt in
          update_repl_ctxt_comp_ctxt rctxt sctxt
      in
      let result := ergoct_eval_decl_via_calculus rctxt decl in
      let out := ergo_string_of_result rctxt result in
      (out, lift_repl_ctxt rctxt result).

  End Interpreter.

  Section InterpreterHack.
    Definition refresh_brand_model_in_comp_ctxt {bm:brand_model} (ctxt:@compilation_context bm) :
      eresult (ErgoCType.tbrand_model * @compilation_context bm) :=
      match ctxt.(compilation_context_new_type_decls) with
      | nil => esuccess (bm, ctxt) nil
      | _ =>
        let all_decls := ctxt.(compilation_context_type_decls) ++ ctxt.(compilation_context_new_type_decls) in
        let new_bm := ErgoTypetoErgoCType.brand_model_of_declarations all_decls in
        elift (fun xy =>
                 let bm := fst xy in
                 let new_ctxt := compilation_context_update_type_declarations ctxt all_decls nil in
                 (bm, new_ctxt)) new_bm
      end.

    Definition refresh_brand_model {bm:brand_model} (ctxt:@repl_context bm) :
      eresult (ErgoCType.tbrand_model * @repl_context bm) :=
      elift (fun xy : ErgoCType.tbrand_model * @compilation_context bm =>
               let (bm, sctxt) := xy in
               (bm, update_repl_ctxt_comp_ctxt ctxt sctxt))
            (@refresh_brand_model_in_comp_ctxt bm ctxt.(repl_context_comp_ctxt)).

  End InterpreterHack.
  
End ErgoDriver.

