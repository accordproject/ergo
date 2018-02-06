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
Require Import Qcert.Common.CommonRuntime.
Require Import JuraBase.
Require Import JuraCalculus.
Require Import Jura.
Require Import JuraSugar.
Require Import ForeignJura.

Section JuratoJavaScript.
  Context {fruntime:foreign_runtime}.
  Context {fjura:foreign_jura}.

  Require Import Qcert.NNRC.NNRCRuntime.

  Section utils.
    Open Scope string.

    Definition brand_of_class_ref (local_package:string) (cr:class_ref) :=
      let pname := 
          match cr.(class_package) with
          | None => local_package
          | Some ref_package => ref_package
          end
      in
      pname ++ "." ++ cr.(class_name).

    Definition lookup_unary_operator fname e :=
      let unop :=
          match fname with
          | "max" => Some OpNumMax
          | "min" => Some OpNumMin
          | "flatten" => Some OpFlatten
          | "toString" => Some OpToString
          | _ => None
          end
      in
      match unop with
      | None => None
      | Some op => Some (NNRCUnop op e)
      end.

    Definition lookup_binary_operator fname e1 e2 :=
      let binop :=
          match fname with
          | "concat" => Some OpStringConcat
          | _ => None
          end
      in
      match binop with
      | None => None
      | Some op => Some (NNRCBinop op e1 e2)
      end.

    Definition lookup_operator (fname:string) (el:list jurac_expr) : option jurac_expr :=
      match el with
      | e :: nil => lookup_unary_operator fname e
      | e1 :: e2 :: nil => lookup_binary_operator fname e1 e2
      | _ => None
      end.

    Definition lookup_builtin (fname:string) (el:list jurac_expr) : option jurac_expr :=
      match fname, el with
      | "now", nil => Some (NNRCGetConstant "now")
      | _, _ => None
      end.
    
    Definition lookup_call (fname:string) (el:list jurac_expr) : option jurac_expr :=
      match lookup_builtin fname el with
      | None =>
        match lookup_operator fname el with
        | None => lookup_foreign fname el
        | Some e => Some e
        end
      | Some e => Some e
      end.
  
    (** [new Concept{ field1: expr1, ... fieldn: exprn }] creates a record and brands it with the concept name *)
    Definition new_expr (brand:string) (struct_expr:nnrc) : nnrc :=
      NNRCUnop (OpBrand (brand :: nil)) struct_expr.

    Definition call_error (fname:string) : nnrc :=
      let msg := "Function " ++ fname ++ " not found" in
      let brand := "org.jura.Error" in
      new_expr brand (NNRCUnop (OpRec "error") (NNRCConst (dstring msg))).

    (** New Array *)
    Definition new_array (el:list jurac_expr) : jurac_expr :=
      match el with
      | nil => NNRCConst (dcoll nil)
      | e1::erest =>
        fold_left (fun acc e => NNRCBinop OpBagUnion (NNRCUnop OpBag e) acc) erest e1
      end.
  End utils.
    
  (** Translate expressions to calculus *)
  Fixpoint jura_expr_to_calculus (local_package:string) (params:list string) (e:jura_expr) : jurac_expr :=
    match e with
    | JVar v => if in_dec string_dec v params then NNRCGetConstant v else NNRCVar v
    | JConst d => NNRCConst d
    | JArray el =>
      let elc := List.map (jura_expr_to_calculus local_package params) el in
      new_array elc
    | JUnaryOp u e =>
      NNRCUnop u (jura_expr_to_calculus local_package params e)
    | JBinaryOp b e1 e2 =>
      NNRCBinop b
                (jura_expr_to_calculus local_package params e1)
                (jura_expr_to_calculus local_package params e2)
    | JIf e1 e2 e3 =>
      NNRCIf (jura_expr_to_calculus local_package params e1)
             (jura_expr_to_calculus local_package params e2)
             (jura_expr_to_calculus local_package params e3)
    | JGuard e1 e2 e3 =>
      NNRCIf (NNRCUnop (OpNeg) (jura_expr_to_calculus local_package params e1))
             (jura_expr_to_calculus local_package params e3)
             (jura_expr_to_calculus local_package params e2)
    | JLet v e1 e2 =>
      NNRCLet v
              (jura_expr_to_calculus local_package params e1)
              (jura_expr_to_calculus local_package params e2)
    | JNew cr nil =>
      new_expr (brand_of_class_ref local_package cr) (NNRCConst (drec nil))
    | JNew cr ((s0,init)::rest) =>
      let init_rec : nnrc := NNRCUnop (OpRec s0) (jura_expr_to_calculus local_package params init) in
      let proc_one (att:string * jura_expr) (acc:nnrc) : nnrc :=
          let attname := fst att in
          let e := jura_expr_to_calculus local_package params (snd att) in
          NNRCBinop OpRecConcat (NNRCUnop (OpRec attname) e) acc
      in
      new_expr (brand_of_class_ref local_package cr) (fold_right proc_one init_rec rest)
    | JThrow cr nil =>
      new_expr (brand_of_class_ref local_package cr) (NNRCConst (drec nil))
    | JThrow cr ((s0,init)::rest) =>
      let init_rec : nnrc := NNRCUnop (OpRec s0) (jura_expr_to_calculus local_package params init) in
      let proc_one (att:string * jura_expr) (acc:nnrc) : nnrc :=
          let attname := fst att in
          let e := jura_expr_to_calculus local_package params (snd att) in
          NNRCBinop OpRecConcat (NNRCUnop (OpRec attname) e) acc
      in
      new_expr (brand_of_class_ref local_package cr) (fold_right proc_one init_rec rest)
    | JFunCall fname el =>
      let elc := List.map (jura_expr_to_calculus local_package params) el in
      match lookup_call fname elc with
      | None => call_error fname
      | Some e => e
      end
    end.
  
  (** Translate a call to a clause to clause+calculus *)
  (** For a clause, add 'this' in the context *)
  Definition clause_to_calculus local_package (c:jura_clause) : jurac_clause :=
    let params := "this"%string :: List.map fst c.(clause_params) in
    mkClause
      c.(clause_name)
      c.(clause_params)
      c.(clause_output)
      c.(clause_throw)
      (jura_expr_to_calculus local_package params c.(clause_code)).

  (** Translate a declaration to a declaration+calculus *)
  Definition declaration_to_calculus local_package (d:jura_declaration) : jurac_declaration :=
    match d with
    | Clause c => Clause (clause_to_calculus local_package c)
    end.

  (** Translate a congract to a contract+calculus *)
  Definition contract_to_calculus local_package (c:jura_contract) : jurac_contract :=
    mkContract
      c.(contract_name)
      c.(contract_template)
      (List.map (declaration_to_calculus local_package) c.(contract_declarations)).

  (** Translate a package to a package+calculus *)
  Definition package_to_calculus (p:package) : jurac_package :=
    let local_package := p.(package_name) in
    mkPackage
      p.(package_name)
      p.(package_imports)
      (contract_to_calculus local_package p.(package_contract)).

End JuratoJavaScript.

