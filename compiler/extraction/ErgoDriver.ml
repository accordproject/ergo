open Assoc
open Datatypes
open Ergo
open ErgoAssembly
open ErgoC
open ErgoCEval
open ErgoCEvalContext
open ErgoCExpand
open ErgoCInline
open ErgoCT
open ErgoCTtoErgoNNRC
open ErgoCTypecheck
open ErgoCTypecheckContext
open ErgoCompContext
open ErgoImptoES6
open ErgoImptoWasmAst
open ErgoNNRC
open ErgoNNRCtoErgoImp
open ErgoNNRCtoJava
open ErgoNameResolve
open ErgoType
open ErgoTypetoQcertType
open ErgoWasmBinary
open ErgotoErgoC
open List0
open Misc
open Names
open NamespaceContext
open PrintTypedData
open Provenance
open QLib
open Result0
open String0
open TBrandModel
open WasmAsttoWasmBinary

(** val resolve_inputs_opt :
    lrergo_input list -> (char list * lrergo_expr) list option ->
    ((laergo_module list * laergo_module option) * namespace_ctxt) eresult **)

let resolve_inputs_opt inputs ftemplate =
  let (p0, p) = triage_ctos_and_ergos inputs in
  let (ctos, mls) = p0 in
  let rctxt = resolve_cto_packages init_namespace_ctxt ctos in
  let mls0 =
    eolift (fun ctxt ->
      elift (fun res -> ((app (fst ctxt) (fst res)), (snd res)))
        (resolve_ergo_modules (snd ctxt) mls)) rctxt
  in
  let mls_and_main =
    eolift (fun xy ->
      let (emods, ctxt) = xy in
      (match p with
       | Some p1 ->
         elift (fun rp -> ((emods, (Some (fst rp))), (snd rp)))
           (resolve_ergo_module ctxt p1)
       | None -> esuccess ((emods, None), ctxt) [])) mls0
  in
  eolift (fun xyz ->
    let (p1, ctxt) = xyz in
    let (emods, p2) = p1 in
    (match ftemplate with
     | Some ftemplate0 ->
       let rtem = resolve_ergo_template ctxt ftemplate0 in
       eolift (fun rtem0 ->
         match rtem0 with
         | [] -> esuccess xyz []
         | _ :: _ ->
           let p3 =
             match p2 with
             | Some p3 -> esuccess p3 []
             | None ->
               empty_main dummy_provenance
                 ('f'::('o'::('r'::('m'::('u'::('l'::('a'::('s'::[]))))))))
                 emods
           in
           elift (fun p4 -> ((emods, (Some
             (add_template_to_module rtem0 p4))), ctxt)) p3) rtem
     | None -> esuccess xyz [])) mls_and_main

(** val resolve_inputs :
    lrergo_input list -> (char list * lrergo_expr) list option ->
    ((laergo_module list * laergo_module) * namespace_ctxt) eresult **)

let resolve_inputs inputs template =
  eolift (fun res ->
    let (y, ctxt) = res in
    let (mls, op) = y in
    (match op with
     | Some p -> esuccess ((mls, p), ctxt) []
     | None -> no_ergo_module_error dummy_provenance))
    (resolve_inputs_opt inputs template)

(** val resolve_inputs_no_main :
    lrergo_input list -> (char list * lrergo_expr) list option ->
    (laergo_module list * namespace_ctxt) eresult **)

let resolve_inputs_no_main inputs template =
  elift (fun res ->
    let (y, ctxt) = res in
    let (mls, op) = y in
    (match op with
     | Some p -> ((app mls (p :: [])), ctxt)
     | None -> (mls, ctxt))) (resolve_inputs_opt inputs template)

(** val just_resolved_inputs :
    lrergo_input list -> (char list * lrergo_expr) list option ->
    laergo_module list eresult **)

let just_resolved_inputs inputs template =
  let resolved = resolve_inputs_no_main inputs template in elift fst resolved

(** val brand_model_from_inputs :
    lrergo_input list -> (QcertType.tbrand_model * laergo_type_declaration
    list) eresult **)

let brand_model_from_inputs inputs =
  let resolved = just_resolved_inputs inputs None in
  let type_decls = elift modules_get_type_decls resolved in
  eolift brand_model_of_declarations type_decls

(** val init_compilation_context_from_inputs :
    brand_model -> lrergo_input list -> (char list * lrergo_expr) list option
    -> laergo_type_declaration list -> ((laergo_module
    list * laergo_module) * compilation_context) eresult **)

let init_compilation_context_from_inputs bm inputs template order =
  let rinputs = resolve_inputs inputs template in
  elift (fun rinputs0 ->
    let (y, ns_ctxt) = rinputs0 in
    (y, (init_compilation_context bm ns_ctxt order))) rinputs

(** val init_compilation_context_from_inputs_no_main :
    brand_model -> lrergo_input list -> (char list * lrergo_expr) list option
    -> laergo_type_declaration list -> (laergo_module
    list * compilation_context) eresult **)

let init_compilation_context_from_inputs_no_main bm inputs template order =
  let rinputs = resolve_inputs_no_main inputs template in
  elift (fun rinputs0 ->
    let (mls, ns_ctxt) = rinputs0 in
    (mls, (init_compilation_context bm ns_ctxt order))) rinputs

(** val ergo_module_to_ergoct :
    brand_model -> compilation_context -> laergo_module ->
    (ergoct_module * compilation_context) eresult **)

let ergo_module_to_ergoct bm ctxt lm =
  let pc = ergo_module_to_calculus bm ctxt lm in
  let pc0 =
    eolift (fun xy ->
      let c = snd xy in
      let order = get_all_decls bm c in
      elift (fun x -> (x, c)) (ergoc_expand_module order (fst xy))) pc
  in
  let pc1 = eolift (fun xy -> ergoc_inline_module bm (snd xy) (fst xy)) pc0 in
  eolift (fun xy ->
    let (mod0, ctxt0) = xy in
    let nsctxt = ctxt0.compilation_context_namespace in
    let sctxt = ctxt0.compilation_context_type_ctxt in
    let pctypes = ergoc_module_typecheck bm nsctxt sctxt mod0 in
    elift (fun xy0 ->
      let (mod1, sctxt') = xy0 in
      (mod1, (compilation_context_update_type_ctxt bm ctxt0 sctxt'))) pctypes)
    pc1

(** val ergo_modules_to_ergoct :
    brand_model -> compilation_context -> laergo_module list ->
    (ergoct_module list * compilation_context) eresult **)

let ergo_modules_to_ergoct bm ctxt lm =
  coq_coq_time
    ('e'::('r'::('g'::('o'::('-'::('>'::('e'::('r'::('g'::('o'::('c'::('('::('t'::('y'::('p'::('e'::('d'::(')'::[]))))))))))))))))))
    (elift_context_fold_left (ergo_module_to_ergoct bm) lm) ctxt

(** val ergo_declaration_to_ergoc :
    brand_model -> compilation_context -> lrergo_declaration ->
    (ergoc_declaration list * compilation_context) eresult **)

let ergo_declaration_to_ergoc bm ctxt ld =
  let ns_ctxt = namespace_ctxt_of_compilation_context bm ctxt in
  let am = resolve_ergo_declaration ns_ctxt ld in
  eolift (fun amc ->
    let ctxt0 = compilation_context_update_namespace bm ctxt (snd amc) in
    elift (fun xy -> ((List0.concat (fst xy)), (snd xy)))
      (elift_context_fold_left (declaration_to_calculus bm) (fst amc) ctxt0))
    am

(** val ergo_declaration_to_ergoct_inlined :
    brand_model -> compilation_context -> lrergo_declaration ->
    (ergoct_declaration list * compilation_context) eresult **)

let ergo_declaration_to_ergoct_inlined bm sctxt decl =
  let ec = ergo_declaration_to_ergoc bm sctxt decl in
  let ec0 =
    eolift (fun xy ->
      let c = snd xy in
      let order = get_all_decls bm c in
      elift (fun x -> (x, c)) (ergoc_expand_declarations order (fst xy))) ec
  in
  let inlined =
    eolift (fun x ->
      let (decls, ctxt) = x in
      elift_context_fold_left (ergoc_inline_declaration bm) decls ctxt) ec0
  in
  eolift (fun xy ->
    elift_context_fold_left (fun sctxt0 decl0 ->
      let nsctxt = sctxt0.compilation_context_namespace in
      elift (fun xy0 ->
        let (declt, tctxt') = xy0 in
        (declt, (compilation_context_update_type_ctxt bm sctxt0 tctxt')))
        (ergoc_decl_typecheck bm nsctxt sctxt0.compilation_context_type_ctxt
          decl0)) (fst xy) (snd xy)) inlined

(** val compilation_context_from_inputs :
    brand_model -> lrergo_input list -> (char list * lrergo_expr) list option
    -> laergo_type_declaration list -> (laergo_module * compilation_context)
    eresult **)

let compilation_context_from_inputs bm inputs template order =
  let cinit = init_compilation_context_from_inputs bm inputs template order in
  eolift (fun init ->
    let (y, ctxt) = init in
    let (mls, p) = y in
    elift (fun r -> (p, (snd r))) (ergo_modules_to_ergoct bm ctxt mls)) cinit

(** val compilation_context_from_inputs_no_main :
    brand_model -> lrergo_input list -> (char list * lrergo_expr) list option
    -> laergo_type_declaration list -> compilation_context eresult **)

let compilation_context_from_inputs_no_main bm inputs template order =
  let cinit =
    init_compilation_context_from_inputs_no_main bm inputs template order
  in
  coq_coq_time
    ('i'::('n'::('i'::('t'::('('::('l'::('o'::('a'::('d'::(' '::('m'::('o'::('d'::('u'::('l'::('e'::('s'::(')'::[]))))))))))))))))))
    (eolift (fun init ->
      let (mls, ctxt) = init in elift snd (ergo_modules_to_ergoct bm ctxt mls)))
    cinit

(** val ergo_module_to_java :
    brand_model -> compilation_context -> laergo_module ->
    (ergo_nnrc_module * QcertCodeGen.java) eresult **)

let ergo_module_to_java bm ctxt p =
  let filename = p.module_prefix in
  let pc = ergo_module_to_ergoct bm ctxt p in
  let pn = eolift (fun xy -> ergoct_module_to_nnrc bm (fst xy)) pc in
  elift (fun x -> (x, (nnrc_module_to_java_top bm filename x))) pn

(** val ergo_module_to_java_top :
    lrergo_input list -> (char list * lrergo_expr) list option -> result_file
    eresult **)

let ergo_module_to_java_top inputs template =
  let bm = brand_model_from_inputs inputs in
  eolift (fun xy ->
    let bm0 = fst xy in
    let cinit = compilation_context_from_inputs bm0 inputs template (snd xy)
    in
    eolift (fun init ->
      let (p, ctxt) = init in
      let res = ergo_module_to_java bm0 ctxt p in
      elift (fun xy0 -> { res_contract_name = None; res_file = p.module_file;
        res_content = (snd xy0) }) res) cinit) bm

(** val ergoc_module_to_es6 :
    brand_model -> char list -> (provenance, absolute_name) ergo_type option
    -> (char list * (provenance, absolute_name) ergo_type_signature) list ->
    ergo_nnrc_module -> QcertCodeGen.ejavascript **)

let ergoc_module_to_es6 bm contract_name contract_state_type sigs p =
  ergo_imp_module_to_es6 bm contract_name contract_state_type sigs
    (ergo_nnrc_module_to_imp bm p)

(** val ergoc_module_to_wasm :
    brand_model -> char list -> ergo_nnrc_module -> wasm **)

let ergoc_module_to_wasm bm contract_name p =
  ergo_wasm_ast_to_ergo_wasm
    (ergo_imp_module_to_wasm_ast bm contract_name
      (ergo_nnrc_module_to_imp bm p))

(** val ergo_module_to_es6_top :
    lrergo_input list -> (char list * lrergo_expr) list option -> result_file
    eresult **)

let ergo_module_to_es6_top inputs template =
  let bm = brand_model_from_inputs inputs in
  eolift (fun xy ->
    let bm0 = fst xy in
    let ctxt = compilation_context_from_inputs bm0 inputs template (snd xy) in
    eolift (fun init ->
      let (p, ctxt0) = init in
      let res =
        let ec = lookup_single_contract p in
        eolift (fun c ->
          let contract_name = fst c in
          let sigs = lookup_contract_signatures (snd c) in
          let pc = ergo_module_to_ergoct bm0 ctxt0 p in
          let pn = eolift (fun xy0 -> ergoct_module_to_nnrc bm0 (fst xy0)) pc
          in
          elift (fun x -> ((contract_name, x),
            (ergoc_module_to_es6 bm0 contract_name (snd c).contract_state
              sigs x))) pn) ec
      in
      elift (fun xyz ->
        let (y, ncontent) = xyz in
        let (contract_name, _) = y in
        { res_contract_name = (Some contract_name); res_file = p.module_file;
        res_content = ncontent }) res) ctxt) bm

(** val ergo_module_to_wasm_top :
    lrergo_input list -> (char list * lrergo_expr) list option -> result_file
    eresult **)

let ergo_module_to_wasm_top inputs template =
  let bm = brand_model_from_inputs inputs in
  eolift (fun xy ->
    let bm0 = fst xy in
    let ctxt = compilation_context_from_inputs bm0 inputs template (snd xy) in
    eolift (fun init ->
      let (p, ctxt0) = init in
      let res =
        let ec = lookup_single_contract p in
        eolift (fun c ->
          let contract_name = fst c in
          let pc = ergo_module_to_ergoct bm0 ctxt0 p in
          let pn = eolift (fun xy0 -> ergoct_module_to_nnrc bm0 (fst xy0)) pc
          in
          elift (fun x -> ((contract_name, x),
            (wasm_to_string (ergoc_module_to_wasm bm0 contract_name x)))) pn)
          ec
      in
      elift (fun xyz ->
        let (y, ncontent) = xyz in
        let (contract_name, _) = y in
        { res_contract_name = (Some contract_name); res_file = p.module_file;
        res_content = ncontent }) res) ctxt) bm

type repl_context = { repl_context_eval_ctxt : eval_context;
                      repl_context_comp_ctxt : compilation_context }

(** val init_repl_context :
    brand_model -> lrergo_input list -> repl_context eresult **)

let init_repl_context bm inputs =
  elift (fun x -> { repl_context_eval_ctxt = empty_eval_context;
    repl_context_comp_ctxt = x })
    (eolift
      (set_namespace_in_compilation_context bm accordproject_top_namespace)
      (compilation_context_from_inputs_no_main bm inputs None []))

(** val update_repl_ctxt_comp_ctxt :
    brand_model -> repl_context -> compilation_context -> repl_context **)

let update_repl_ctxt_comp_ctxt _ rctxt sctxt =
  { repl_context_eval_ctxt = rctxt.repl_context_eval_ctxt;
    repl_context_comp_ctxt = sctxt }

(** val update_repl_ctxt_type_ctxt :
    brand_model -> repl_context -> type_context -> repl_context **)

let update_repl_ctxt_type_ctxt bm rctxt nctxt =
  update_repl_ctxt_comp_ctxt bm rctxt
    (compilation_context_update_type_ctxt bm rctxt.repl_context_comp_ctxt
      nctxt)

(** val update_repl_ctxt_eval_ctxt :
    brand_model -> repl_context -> eval_context -> repl_context **)

let update_repl_ctxt_eval_ctxt _ rctxt nctxt =
  { repl_context_eval_ctxt = nctxt; repl_context_comp_ctxt =
    rctxt.repl_context_comp_ctxt }

(** val lift_repl_ctxt :
    brand_model -> repl_context -> ((qcert_type option * qcert_data
    option) * repl_context) eresult -> repl_context **)

let lift_repl_ctxt _ orig_ctxt result =
  elift_both snd (fun _ -> orig_ctxt) result

(** val ergoc_repl_eval_declaration :
    brand_model -> repl_context -> ergoct_declaration -> ((qcert_type
    option * qcert_data option) * repl_context) eresult **)

let ergoc_repl_eval_declaration bm ctxt decl =
  let nsctxt = ctxt.repl_context_comp_ctxt.compilation_context_namespace in
  let typ = ergoct_declaration_type bm decl in
  let warnings = ctxt.repl_context_comp_ctxt.compilation_context_warnings in
  let init =
    eolift (ergoct_eval_decl bm ctxt.repl_context_eval_ctxt)
      (esuccess decl warnings)
  in
  eolift (fun xy ->
    let (dctxt', od) = xy in
    (match od with
     | Some out ->
       (match unpack_output out with
        | Some p ->
          let (_, state) = p in
          let newctxt =
            match typ with
            | Some typ0 ->
              elift (fun ty ->
                let (_, statety) = ty in
                let ctxt1 =
                  update_repl_ctxt_eval_ctxt bm ctxt
                    (eval_context_update_global_env dctxt' this_state state)
                in
                let sctxt1 =
                  ctxt1.repl_context_comp_ctxt.compilation_context_type_ctxt
                in
                update_repl_ctxt_type_ctxt bm ctxt1
                  (type_context_update_global_env bm.brand_model_relation
                    sctxt1 this_state statety))
                (unpack_success_type bm nsctxt typ0 warnings)
            | None ->
              esuccess
                (update_repl_ctxt_eval_ctxt bm ctxt
                  (eval_context_update_global_env dctxt' this_state state))
                warnings
          in
          elift (fun ctxt0 -> ((typ, (Some out)), ctxt0)) newctxt
        | None ->
          esuccess ((typ, (Some out)),
            (update_repl_ctxt_eval_ctxt bm ctxt dctxt')) [])
     | None ->
       esuccess ((typ, None), (update_repl_ctxt_eval_ctxt bm ctxt dctxt')) []))
    init

(** val ergoct_repl_eval_declarations :
    brand_model -> repl_context -> ergoct_declaration list -> ((qcert_type
    option * qcert_data option) * repl_context) eresult **)

let ergoct_repl_eval_declarations bm ctxt decls =
  elift (fun xy -> ((last_some_pair (fst xy)), (snd xy)))
    (elift_context_fold_left (ergoc_repl_eval_declaration bm) decls ctxt)

(** val ergoct_eval_decl_via_calculus :
    brand_model -> repl_context -> lrergo_declaration -> ((qcert_type
    option * qcert_data option) * repl_context) eresult **)

let ergoct_eval_decl_via_calculus bm ctxt decl =
  eolift_warning (fun xyw ->
    let (p, warnings) = xyw in
    let (decls, sctxt') = p in
    let sctxt'0 = compilation_context_add_warnings bm sctxt' warnings in
    let rctxt' = update_repl_ctxt_comp_ctxt bm ctxt sctxt'0 in
    ergoct_repl_eval_declarations bm rctxt' decls)
    (ergo_declaration_to_ergoct_inlined bm ctxt.repl_context_comp_ctxt decl)

(** val ergo_string_of_result :
    brand_model -> repl_context -> ((qcert_type option * qcert_data
    option) * repl_context) eresult -> char list eresult **)

let ergo_string_of_result bm rctxt result =
  let nsctxt = rctxt.repl_context_comp_ctxt.compilation_context_namespace in
  let global_env = rctxt.repl_context_eval_ctxt.eval_context_global_env in
  let old_state = lookup string_dec global_env this_state in
  elift (string_of_typed_result bm nsctxt old_state) (elift fst result)

(** val ergoct_repl_eval_decl :
    brand_model -> repl_context -> lrergo_declaration -> char list
    eresult * repl_context **)

let ergoct_repl_eval_decl bm rctxt decl =
  let rctxt0 =
    let sctxt = rctxt.repl_context_comp_ctxt in
    let sctxt0 = compilation_context_reset_warnings bm sctxt in
    update_repl_ctxt_comp_ctxt bm rctxt sctxt0
  in
  let result = ergoct_eval_decl_via_calculus bm rctxt0 decl in
  let out = ergo_string_of_result bm rctxt0 result in
  (out, (lift_repl_ctxt bm rctxt0 result))

(** val refresh_brand_model_in_comp_ctxt :
    brand_model -> compilation_context ->
    (QcertType.tbrand_model * compilation_context) eresult **)

let refresh_brand_model_in_comp_ctxt bm ctxt =
  match ctxt.compilation_context_new_type_decls with
  | [] -> esuccess (bm, ctxt) []
  | _ :: _ ->
    let all_decls =
      app ctxt.compilation_context_type_decls
        ctxt.compilation_context_new_type_decls
    in
    let new_bm = brand_model_of_declarations all_decls in
    elift (fun xy ->
      let bm0 = fst xy in
      let new_ctxt =
        compilation_context_update_type_declarations bm ctxt all_decls []
      in
      (bm0, new_ctxt)) new_bm

(** val refresh_brand_model :
    brand_model -> repl_context -> (QcertType.tbrand_model * repl_context)
    eresult **)

let refresh_brand_model bm ctxt =
  elift (fun xy ->
    let (bm0, sctxt) = xy in (bm0, (update_repl_ctxt_comp_ctxt bm ctxt sctxt)))
    (refresh_brand_model_in_comp_ctxt bm ctxt.repl_context_comp_ctxt)
