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

(* This is the [WIP] REFERENCE IMPLEMENTATION of the dynamic semantics of the
 * ERGO language.
 *
 * It is also being developed, and changing rapidly.
 *
 * -- Kartik, June 2018
 *)

Require Import String.
Require Import List.
Require Import Basics.

Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.EUtil.
Require Import ErgoSpec.Common.Utils.EResult.
Require Import ErgoSpec.Common.Utils.EProvenance.
Require Import ErgoSpec.Common.Pattern.EPattern.

Require Import ErgoSpec.ErgoC.Lang.ErgoC.
Require Import ErgoSpec.ErgoC.Lang.ErgoCTypeContext.

Require Import ErgoSpec.Ergo.Lang.Ergo.
Require Import Qcert.Common.TypeSystem.RTypetoJSON.

Require Import ErgoSpec.Translation.ErgoTypetoErgoCType.

Section ErgoCType.
  Context {m : brand_model}.

  Import ErgoCTypes.

  Program Definition empty_rec_type : ergoc_type := Rec Closed nil _.
  Fixpoint ergo_type_expr (ctxt : type_context) (expr : ergoc_expr) : eresult ergoc_type :=
    match expr with
    | EThisContract prov => efailure (ESystemError prov "No `this' in ergoc")
    | EThisClause   prov => efailure (ESystemError prov "No `clause' in ergoc")
    | EThisState    prov => efailure (ESystemError prov "No `state' in ergoc")
    | EVar prov name =>
      let opt := lookup String.string_dec (ctxt.(type_context_local_env)++ctxt.(type_context_global_env)) name in
      eresult_of_option opt (ERuntimeError prov ("Variable not found: " ++ name)%string)
    | EConst prov d =>
      eresult_of_option
        (infer_data_type d)
        (ETypeError prov "Bad constant.")
    | EArray prov es =>
      (elift tcoll)
        (fold_left
           (fun T new =>
              eolift
                (fun T' =>
                   elift
                     (fun new' => ergoc_type_meet T' new')
                     (ergo_type_expr ctxt new))
                T)
           es (esuccess ttop))
    | EUnaryOp prov op e =>
      match ergo_type_expr ctxt e with
      | Success _ _ e' =>
        match ergoc_type_infer_unary_op op e' with
        | Some (r, _) => esuccess r
        | None => efailure (ETypeError prov "Ill-typed unary operation."%string)
        end
      | Failure _ _ f => efailure f
      end
    | EBinaryOp prov op e1 e2 =>
      match ergo_type_expr ctxt e1 with
      | Success _ _ e1' =>
        match ergo_type_expr ctxt e2 with
        | Success _ _ e2' =>
          match ergoc_type_infer_binary_op op e1' e2' with
          | Some (r, _, _) => esuccess r
          | None => efailure (ETypeError prov "Ill-typed binary operation."%string)
          end
        | Failure _ _ f => efailure f
        end
      | Failure _ _ f => efailure f
      end
    | EIf prov c t f =>
      eolift (fun c' =>
                if ergoc_type_subtype_dec c' tbool then
                  elift2 ergoc_type_meet
                         (ergo_type_expr ctxt t)
                         (ergo_type_expr ctxt f)
                else efailure (ETypeError prov "'If' condition not boolean."%string))
             (ergo_type_expr ctxt c)
    | ELet prov n None v e =>
      (eolift (fun vt =>
                let ctxt' := type_context_update_local_env ctxt n vt in
                ergo_type_expr ctxt' e)
             (ergo_type_expr ctxt v))
    | ELet prov n (Some t) v e =>
      (eolift
         (fun vt =>
            let t' := (ergo_type_to_ergoc_type t) in
            if subtype_dec vt t' then
              let ctxt' :=
                  type_context_update_local_env
                    ctxt n
                    t'
              in
              ergo_type_expr ctxt' e
            else
              efailure (ETypeError prov "`Let' type mismatch."))
         (ergo_type_expr ctxt v))
    | ERecord prov rs =>
      fold_left
        (fun sofar next =>
           eolift2
             (fun sofar' val' =>
                (elift (compose fst fst))
                  (eresult_of_option
                     (ergoc_type_infer_binary_op OpRecConcat sofar' val')
                     (ETypeError prov "Bad record! Failed to concat."%string)))
             sofar
             (eolift (fun val =>
                        (elift fst)
                          (eresult_of_option
                             (ergoc_type_infer_unary_op (OpRec (fst next)) val)
                             (ETypeError prov "Bad record! Failed to init."%string)))
                     (ergo_type_expr ctxt (snd next))))
        rs (esuccess empty_rec_type)
    | ENew prov name rs =>
      eolift
        (fun rs' =>
           (elift fst)
             (eresult_of_option
                (ergoc_type_infer_unary_op
                   (OpBrand (name::nil)) rs')
                (ETypeError prov "Concept name doesn't match data"%string)))
        (fold_left
           (fun sofar next =>
              eolift2
                (fun sofar' val' =>
                   (elift (compose fst fst))
                     (eresult_of_option
                        (ergoc_type_infer_binary_op OpRecConcat sofar' val')
                        (ETypeError prov "Bad record! Failed to concat."%string)))
                sofar
                (eolift (fun val =>
                           (elift fst)
                             (eresult_of_option
                                (ergoc_type_infer_unary_op (OpRec (fst next)) val)
                                (ETypeError prov "Bad record! Failed to init."%string)))
                        (ergo_type_expr ctxt (snd next))))
           rs (esuccess empty_rec_type))
    | ECallFun prov fname args => function_not_inlined_error prov fname
    | ECallFunInGroup prov gname fname args => function_in_group_not_inlined_error prov gname fname

    | EMatch prov term pes default => TODO prov "type match"
      (*
      let lift_dbrand :=
          fun dat brand fn default =>
            match dat with
            | dbrand (br::nil) rcd =>
              if String.string_dec brand br then
                fn dat
              else
                default
            | _ => default
            end
      in
      match ergo_type_expr ctxt term with
      | Failure _ _ f => efailure f
      | Success _ _ dat =>
        fold_left
          (fun default_result pe =>
             match pe with
             | (CaseData prov d, res) => (* TODO can `d' ever be bad? *)
               elift2 ergoc_type_meet default_result (ergo_type_expr ctxt res)
             | (CaseWildcard prov None, res) =>
               elift2 ergoc_type_meet default_result (ergo_type_expr ctxt res)
             | (CaseLet prov name None, res) =>
               elift2 ergoc_type_meet default_result
                      (ergo_type_expr (type_context_update_local_env ctxt name dat) res)
             | (CaseLetOption prov name None, res) =>
               match dat with
               | dright dunit => default_result
               | dleft dat' => ergo_type_expr (type_context_update_local_env ctxt name dat') res
               | _ =>
                 efailure (RuntimeError prov "Matched LetOption without an option.")
               end
             | (CaseWildcard prov (Some typ), res) =>
               lift_dbrand dat typ
                           (fun dat' => ergo_type_expr ctxt res)
                           default_result
             | (CaseLet prov name (Some typ), res) =>
               lift_dbrand dat typ
                           (fun dat' => ergo_type_expr
                                          (type_context_update_local_env ctxt name dat')
                                          res)
                           default_result
             | (CaseLetOption prov name (Some typ), res) =>
               match dat with
               | dright dunit => default_result
               | dleft dat' =>
                 lift_dbrand dat' typ
                             (fun dat' => ergo_type_expr
                                            (type_context_update_local_env ctxt name dat')
                                            res)
                             default_result
               | _ =>
                 efailure (RuntimeError prov "Matched LetOption without an option.")
               end
             end)
          pes (ergo_type_expr ctxt default)
      end
*)

    (* EXPECTS: each foreach has only one dimension and no where *)
    | EForeach prov ((name,arr)::nil) None fn =>
      eolift (fun arr' =>
                eolift
                  (fun typ => (elift tcoll) (ergo_type_expr (type_context_update_local_env ctxt name typ) fn))
                (eresult_of_option
                  (untcoll arr')
                  (ETypeError prov "foreach must be called with array")))
            (ergo_type_expr ctxt arr)
            
    | EForeach prov _ _ _ =>
      complex_foreach_in_calculus_error prov
    end.

  Definition ergoc_type_decl
             (dctxt : type_context)
             (decl : ergoc_declaration)
    : eresult (type_context * option ergoc_type) :=
    match decl with
    | DCExpr prov expr =>
      elift (fun x => (dctxt, Some x)) (ergo_type_expr dctxt expr)
    | DCConstant prov name expr =>
      let expr' := ergo_type_expr dctxt expr in
      eolift (fun val => esuccess (type_context_update_global_env dctxt name val, None)) expr'
    | DCFunc prov name func =>
      esuccess (dctxt, None)
    | DCContract prov name contr =>
      esuccess (dctxt, None)
    end.

End ErgoCType.

Section TestModel.
  Import ErgoCTypes.

  Local Open Scope string.

  (* For the CTO:
     ============

     concept Entity {}
     concept Customer extends Entity { o Integer age o Integer cid o String name }
     concept Purchase extends Entity { o Integer cid o String name o Integer pid o Integer quantity }
   *)

  Definition StoreHierarchy :=
    ("org.accordproject.ergotop.Customer","org.accordproject.ergotop.Entity")::("org.accordproject.ergotop.Purchase","org.accordproject.ergotop.Entity")::nil.

  Definition StoreBrandRelationMaybe : eresult tbrand_relation
    := eresult_of_qresult dummy_provenance (mk_tbrand_relation StoreHierarchy).

  Definition StoreBrandRelation : brand_relation :=
    match StoreBrandRelationMaybe with
    | Success _ _ s => s
    | Failure _ _ e => tempty_brand_relation (* Not used *)
    end.

  (* Compute StoreBrandModelMaybe. *)
  
  Existing Instance StoreBrandRelation.

  Program Definition EntityType : ergoc_type
    := Rec Open nil _.

  Program Definition CustomerType : ergoc_type
    := Rec Open (("age", Nat)
                 :: ("cid", Nat)
                 :: ("name", String)
                 :: nil) _.

  Program Definition PurchaseType : ergoc_type
    := Rec Open (("cid", Nat)
                 :: ("name", String)
                 :: ("pid", Nat)
                 :: ("quantity", Nat)
                 :: nil) _.

  Definition StoreModelTypeDecls : tbrand_context_decls :=
    (("org.accordproject.ergotop.Customer", CustomerType)
     :: ("org.accordproject.ergotop.Entity", EntityType)
     :: ("org.accordproject.ergotop.Purchase", PurchaseType)
     :: nil).

  Definition StoreBrandModelMaybe : eresult tbrand_model
    := eresult_of_qresult dummy_provenance
                          (mk_tbrand_model StoreModelTypeDecls).

  (* Compute StoreBrandModelMaybe. *)
  
  Instance StoreBrandModel : brand_model :=
    match StoreBrandModelMaybe with
    | Success _ _ s => s
    | Failure _ _ e => tempty_brand_model (* Not used *)
    end.

  Definition try_it (e:ergoc_expr) : eresult ectype_struct :=
    elift unpack_ergoc_type (@ergo_type_expr StoreBrandModel empty_type_context e).

  (* Compute (try_it (EConst dummy_provenance (dunit))). *) (* success - Unit *)
  (* Compute (try_it (EConst dummy_provenance (dstring "pooh"))). *) (* success - String *)
  (* Compute (try_it (EConst dummy_provenance (dnat 14))). *) (* success - Nat *)
  (* Compute (try_it (EConst dummy_provenance (dbrand ("Customer"::nil) (drec (("age",dnat 14)::("cid",dnat 0)::("name",dstring "pooh")::nil))))). *) (* success - Customer *)
  (* Compute (try_it (EConst dummy_provenance (dbrand ("Entity"::nil) (drec (("a",dunit)::nil))))). *) (* success - Entity *)
  
  (* Compute (try_it (EConst dummy_provenance (dbrand ("Customer"::nil) (drec (("a",dunit)::nil))))). *) (* success to top - ?? semantics for it needs to be checked *)

  (* Compute (try_it (EConst dummy_provenance (dbrand ("Customer"::nil) (drec (("age",dnat 14)::("cid",dnat 0)::("name",dstring "pooh")::nil))))). *) (* success - Customer *)
  
  (* Compute (try_it (EConst dummy_provenance (dbrand ("Customer"::nil) (drec (("age",dnat 14)::("name",dstring "pooh")::nil))))). *) (* success to top - ?? semantics for it needs to be checked *)

  (* Compute (try_it (EUnaryOp dummy_provenance OpUnbrand (EConst dummy_provenance (dbrand ("Customer"::nil) (drec (("age",dnat 14)::("cid",dnat 0)::("name",dstring "pooh")::nil)))))). *) (* success - { age : Nat, cid : Nat, name : String, .. } *)

  (* Compute (try_it (EUnaryOp dummy_provenance (OpBrand ("Customer"::nil)) (EConst dummy_provenance (drec (("age",dnat 14)::("cid",dnat 0)::("name",dstring "pooh")::nil))))). *) (* success - Customer *)

  (* Compute (try_it (EUnaryOp dummy_provenance (OpBrand ("Customer"::nil)) (EConst dummy_provenance (drec (("age",dnat 14)::("name",dstring "pooh")::nil))))). *) (* Failure - subtyping *)

  (* Compute (try_it (EUnaryOp dummy_provenance (OpDot "name") (EUnaryOp dummy_provenance OpUnbrand (((EConst dummy_provenance (dbrand ("Customer"::nil) (drec (("age",dnat 14)::("cid",dnat 0)::("name",dstring "pooh")::nil))))))))). *) (* success - String *)
  
End TestModel.
