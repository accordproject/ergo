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

Require Import Qcert.Utils.Utils.
Require Import Qcert.Common.CommonRuntime.

Require Import Error.
Require Import JuraBase.
Require Import JuraCalculus.
Require Import JuraCalculusCall.
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

    (** New Array *)
    Definition new_array (el:list jurac_expr) : jurac_expr :=
      match el with
      | nil => NNRCConst (dcoll nil)
      | e1::erest =>
        fold_left (fun acc e => NNRCBinop OpBagUnion (NNRCUnop OpBag e) acc) erest (NNRCUnop OpBag e1)
      end.

    (** [new Concept{ field1: expr1, ... fieldn: exprn }] creates a record and brands it with the concept name *)
    Definition new_expr (brand:string) (struct_expr:jurac_expr) : jurac_expr :=
      NNRCUnop (OpBrand (brand :: nil)) struct_expr.
  End utils.

  Section stdlib.
    Local Open Scope string.

    Definition mk_naked_closure (params:list string) (body:jurac_expr) :=
      let params := List.map (fun x => (x,None)) params in
      mkClosure
        params
        None
        None
        body.
    
    Definition unary_operator_table : lookup_table :=
      fun fname =>
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
        | Some op =>
          Some (mk_naked_closure
                  ("p1"::nil)
                  (NNRCUnop op (NNRCGetConstant "p1")))
        end.

    Definition binary_operator_table : lookup_table :=
      fun fname =>
        let binop :=
            match fname with
            | "concat" => Some OpStringConcat
            | _ => None
            end
        in
        match binop with
        | None => None
        | Some op =>
          Some (mk_naked_closure
                  ("p1"::"p2"::nil)
                  (NNRCBinop op (NNRCGetConstant "p1") (NNRCGetConstant "p2")))
        end.

    Definition builtin_table : lookup_table :=
      fun fname =>
        match fname with
        | "now" =>
          Some (mk_naked_closure
                  nil
                  (NNRCGetConstant "now"))
        | _ => None
        end.

    Definition stdlib :=
      compose_table foreign_table
                    (compose_table builtin_table
                                   (compose_table unary_operator_table binary_operator_table)).

  End stdlib.

  Record context :=
    mkContext {
        context_table: lookup_table;
        context_package: string;
        context_globals: list string;
        context_params: list string;
      }.

  Definition add_globals (ctxt:context) (params:list string) : context :=
    mkContext
      ctxt.(context_table)
      ctxt.(context_package)
      (List.app params ctxt.(context_globals))
      ctxt.(context_params).

  Definition add_params (ctxt:context) (params:list string) : context :=
    mkContext
      ctxt.(context_table)
      ctxt.(context_package)
      ctxt.(context_globals)
      (List.app params ctxt.(context_params)).

  Definition add_one_global (ctxt:context) (param:string) : context :=
    mkContext
      ctxt.(context_table)
      ctxt.(context_package)
      (List.cons param ctxt.(context_globals))
      ctxt.(context_params).

  Definition add_one_param (ctxt:context) (param:string) : context :=
    mkContext
      ctxt.(context_table)
      ctxt.(context_package)
      ctxt.(context_globals)
      (List.cons param ctxt.(context_params)).

  Definition add_one_func (ctxt:context) (fname:string) (fclosure:closure) :=
    mkContext
      (add_function_to_table ctxt.(context_table) fname fclosure)
      ctxt.(context_package)
      ctxt.(context_globals)
      ctxt.(context_params).

  Definition cswitch_cases :=
    list (switch_case * jurac_expr).

  Section fresh_vars.
    Require Import Fresh.
    Definition fresh_in_switch {A} (eccases:list (A * jurac_expr)) (ecdefault:jurac_expr) :=
      fresh_var
        "$switch"
        (List.app
           (List.concat
              (List.map (fun eccase => nnrc_free_vars (snd eccase)) eccases))
           (nnrc_free_vars ecdefault)).
    Definition fresh_in_case (e:jurac_expr) :=
      fresh_var "$case"
                (nnrc_free_vars e).
  End fresh_vars.

  (** Translate expressions to calculus *)
  Fixpoint jura_expr_to_calculus
           (ctxt:context) (e:jura_expr) : jresult jurac_expr :=
    match e with
    | JVar v =>
      if in_dec string_dec v ctxt.(context_params)
      then jsuccess (NNRCGetConstant v)
      else jsuccess (NNRCVar v)
    | JConst d =>
      jsuccess (NNRCConst d)
    | JArray el =>
      let init_el := jsuccess nil in
      let proc_one (acc:jresult (list jurac_expr)) (e:jura_expr) : jresult (list jurac_expr) :=
          jlift2
            cons
            (jura_expr_to_calculus ctxt e)
            acc
      in
      jlift new_array (fold_left proc_one el init_el)
    | JUnaryOp u e =>
      jlift (NNRCUnop u)
            (jura_expr_to_calculus ctxt e)
    | JBinaryOp b e1 e2 =>
      jlift2 (NNRCBinop b)
             (jura_expr_to_calculus ctxt e1)
             (jura_expr_to_calculus ctxt e2)
    | JIf e1 e2 e3 =>
      jlift3 NNRCIf
        (jura_expr_to_calculus ctxt e1)
        (jura_expr_to_calculus ctxt e2)
        (jura_expr_to_calculus ctxt e3)
    | JGuard e1 e2 e3 =>
      jlift3 NNRCIf
        (jlift (NNRCUnop (OpNeg)) (jura_expr_to_calculus ctxt e1))
        (jura_expr_to_calculus ctxt e3)
        (jura_expr_to_calculus ctxt e2)
    | JLet v e1 e2 =>
      jlift2 (NNRCLet v)
              (jura_expr_to_calculus ctxt e1)
              (jura_expr_to_calculus ctxt e2)
    | JNew cr nil =>
      jsuccess
        (new_expr (brand_of_class_ref ctxt.(context_package) cr) (NNRCConst (drec nil)))
    | JNew cr ((s0,init)::rest) =>
      let init_rec : jresult nnrc :=
          jlift (NNRCUnop (OpRec s0)) (jura_expr_to_calculus ctxt init)
      in
      let proc_one (acc:jresult nnrc) (att:string * jura_expr) : jresult nnrc :=
          let attname := fst att in
          let e := jura_expr_to_calculus ctxt (snd att) in
          jlift2 (NNRCBinop OpRecConcat)
                 (jlift (NNRCUnop (OpRec attname)) e) acc
      in
      jlift (new_expr (brand_of_class_ref ctxt.(context_package) cr)) (fold_left proc_one rest init_rec)
    | JThrow cr nil =>
      jsuccess (new_expr (brand_of_class_ref ctxt.(context_package) cr) (NNRCConst (drec nil)))
    | JThrow cr ((s0,init)::rest) =>
      let init_rec : jresult nnrc :=
          jlift (NNRCUnop (OpRec s0)) (jura_expr_to_calculus ctxt init)
      in
      let proc_one (acc:jresult nnrc) (att:string * jura_expr) : jresult nnrc :=
          let attname := fst att in
          let e := jura_expr_to_calculus ctxt (snd att) in
          jlift2 (NNRCBinop OpRecConcat)
                 (jlift (NNRCUnop (OpRec attname)) e)
                 acc
      in
      jlift (new_expr (brand_of_class_ref ctxt.(context_package) cr)) (fold_left proc_one rest init_rec)
    | JFunCall fname el =>
      let init_el := jsuccess nil in
      let proc_one (e:jura_expr) (acc:jresult (list jurac_expr)) : jresult (list jurac_expr) :=
          jlift2
            cons
            (jura_expr_to_calculus ctxt e)
            acc
      in
      jolift (lookup_call ctxt.(context_table) fname) (fold_right proc_one init_el el)
    | JSwitch e0 ecases edefault =>
      let ec0 := jura_expr_to_calculus ctxt e0 in
      let eccases :=
          let proc_one acc ecase :=
              jolift
                (fun acc =>
                   jlift (fun x => (fst ecase, x)::acc)
                         (jura_expr_to_calculus ctxt (snd ecase))) acc
          in
          fold_left proc_one ecases (jsuccess nil)
      in
      let ecdefault := jura_expr_to_calculus ctxt edefault in
      jolift
        (fun ec0 =>
           jolift
             (fun eccases =>
                jolift
                  (fun ecdefault =>
                     let v0 := fresh_in_switch eccases ecdefault in
                     let proc_one_case
                           (acc:jresult jurac_expr)
                           (ecase:switch_case * jurac_expr)
                         : jresult jurac_expr :=
                         match fst ecase with
                         | (Some v, CaseValue d) =>
                           jlift
                             (fun acc =>
                                NNRCIf (NNRCBinop OpEqual
                                                  (NNRCVar v0)
                                                  (NNRCConst d))
                                       (NNRCLet v
                                                (NNRCVar v0)
                                                (snd ecase))
                                       acc) acc
                         | (None, CaseValue d) =>
                           jlift
                             (fun acc =>
                                NNRCIf (NNRCBinop OpEqual
                                                  (NNRCVar v0)
                                                  (NNRCConst d))
                                       (snd ecase)
                                       acc) acc
                         | (Some v, CaseType brand) =>
                           jlift (fun acc =>
                                    let v2 := fresh_in_case acc in
                                    NNRCEither
                                      (NNRCUnop (OpCast (brand::nil)) (NNRCVar v0))
                                      v (snd ecase)
                                      v2 acc
                                 ) acc
                         | (None, CaseType brand) =>
                           jlift (fun acc =>
                                    let v1 := fresh_in_case (snd ecase) in
                                    let v2 := fresh_in_case acc in
                                    NNRCEither
                                      (NNRCUnop (OpCast (brand::nil)) (NNRCVar v0))
                                      v1 (snd ecase)
                                      v2 acc
                                 ) acc
                         end
                     in
                     let eccases_folded :=
                         fold_left proc_one_case eccases (jsuccess ecdefault)
                     in
                     jlift (NNRCLet v0 ec0) eccases_folded)
                  ecdefault) eccases) ec0
    | JFor v e1 None e2 =>
      jlift2 (NNRCFor v)
              (jura_expr_to_calculus ctxt e1)
              (jura_expr_to_calculus ctxt e2)
    | JFor v e1 (Some econd) e2 =>
      jlift3 (fun e1 econd e3 =>
                NNRCUnop OpFlatten
                         (NNRCFor v
                                  (NNRCUnop OpBag e1)
                                  (NNRCIf econd e3 (NNRCConst (dcoll nil)))))
             (jura_expr_to_calculus ctxt e1)
             (jura_expr_to_calculus ctxt econd)
             (jura_expr_to_calculus ctxt e2)
    end.

  (** Translate a clause to clause+calculus *)
  (** For a clause, add 'this' and 'now' to the context *)

  Definition clause_to_calculus
             (ctxt:context) (c:jura_clause) : jresult jurac_clause :=
    let ctxt : context :=
        add_params
          ctxt
          ("this"%string :: "now"%string :: List.map fst c.(clause_closure).(closure_params))
    in
    jlift
      (mkClause
         c.(clause_name))
      (jlift
         (mkClosure
            c.(clause_closure).(closure_params)
            c.(clause_closure).(closure_output)
            c.(clause_closure).(closure_throw))
         (jura_expr_to_calculus ctxt c.(clause_closure).(closure_body))).

  (** Translate a function to function+calculus *)
  Definition func_to_calculus
             (ctxt:context) (f:jura_func) : jresult jurac_func :=
    let ctxt :=
        add_params ctxt (List.map fst f.(func_closure).(closure_params))
    in
    jlift
      (mkFunc
         f.(func_name))
      (jlift
         (mkClosure
            f.(func_closure).(closure_params)
            f.(func_closure).(closure_output)
            f.(func_closure).(closure_throw))
         (jura_expr_to_calculus ctxt f.(func_closure).(closure_body))).

  (** Translate a declaration to a declaration+calculus *)
  Definition declaration_to_calculus
             (ctxt:context) (d:jura_declaration) : jresult (context * jurac_declaration) :=
    match d with
    | Clause c =>
      jlift
        (fun x => (add_one_func ctxt x.(clause_name) x.(clause_closure), Clause x)) (* Add new function to context *)
        (clause_to_calculus ctxt c)
    | Func f =>
      jlift
        (fun x => (add_one_func ctxt x.(func_name) x.(func_closure), Func x)) (* Add new function to context *)
        (func_to_calculus ctxt f)
    end.

  (** Translate a contract to a contract+calculus *)
  Definition contract_to_calculus
             (ctxt:context) (c:jura_contract) : jresult jurac_contract :=
    let init := jsuccess (ctxt, nil) in
    let proc_one
          (acc:jresult (context * list jurac_declaration))
          (s:jura_declaration)
        : jresult (context * list jurac_declaration) :=
        jolift
          (fun acc : context * list jurac_declaration =>
             let (ctxt,acc) := acc in
             jlift (fun xy : context * jurac_declaration =>
                      let (newctxt,news) := xy in
                      (newctxt,news::acc))
                   (declaration_to_calculus ctxt s))
          acc
    in
    jlift
      (fun xy =>
         (mkContract
            c.(contract_name)
            c.(contract_template)
           (snd xy)))
      (List.fold_left proc_one c.(contract_declarations) init).

  (** Translate a statement to a statement+calculus *)
  Definition stmt_to_calculus
             (ctxt:context) (s:jura_stmt) : jresult (context * jurac_stmt) :=
    match s with
    | JExpr e =>
      jlift
        (fun x => (ctxt, JExpr x))
        (jura_expr_to_calculus ctxt e)
    | JGlobal v e =>
      jlift
        (fun x => (add_one_global ctxt v, JGlobal v x)) (* Add new variable to context *)
        (jura_expr_to_calculus ctxt e)
    | JImport s =>
      jsuccess (ctxt, JImport s)
    | JFunc f =>
      jlift
        (fun x => (add_one_func ctxt x.(func_name) x.(func_closure), JFunc x)) (* Add new function to context *)
        (func_to_calculus ctxt f)
    | JContract c =>
      jlift (fun x => (ctxt, JContract x))
            (contract_to_calculus ctxt c)
    end.

  Definition initial_context (p:string) :=
    mkContext stdlib p nil nil.

  (** Translate a package to a package+calculus *)
  Definition package_to_calculus (p:package) : jresult jurac_package :=
    let local_package := p.(package_name) in
    let ctxt := initial_context local_package in
    let init := jsuccess (ctxt, nil) in
    let proc_one
          (acc:jresult (context * list jurac_stmt))
          (s:jura_stmt)
        : jresult (context * list jurac_stmt) :=
        jolift
          (fun acc : context * list jurac_stmt =>
             let (ctxt,acc) := acc in
             jlift (fun xy : context * jurac_stmt =>
                      let (newctxt,news) := xy in
                      (newctxt,news::acc))
                   (stmt_to_calculus ctxt s))
          acc
    in
    jlift
      (fun xy =>
         (mkPackage
            p.(package_name)
            (snd xy)))
      (List.fold_left proc_one p.(package_statements) init).

  Section tests.
    Open Scope string.
    Definition ctxt0 := initial_context "test".

    Definition input1 := dnat 2.
    
    Example j1 :=
      JSwitch (JConst input1)
              (((Some "v1", CaseValue (dnat 1)), (JConst (dstring "1")))
                 :: ((Some "v2", CaseValue (dnat 2)), (JConst (dstring "2")))
                 :: nil)
              (JConst (dstring "lots")).
    Definition jc1 := jura_expr_to_calculus ctxt0 j1.
    (* Eval vm_compute in jc1. *)
    (* Eval vm_compute in jlift (fun x => nnrc_eval_top nil x nil) jc1. *)

    Example j1' :=
      JSwitch (JConst input1)
              (((Some "v1", CaseValue (dnat 1)), (JConst (dstring "1")))
                 :: ((Some "v2", CaseValue (dnat 2)), JVar "v2")
                 :: nil)
              (JConst (dstring "lots")).
    Definition jc1' := jura_expr_to_calculus ctxt0 j1'.
    (* Eval vm_compute in jc1'. *)
    (* Eval vm_compute in jlift (fun x => nnrc_eval_top nil x nil) jc1'. *)

    Definition input2 :=
      dbrand ("C1"::nil) (dnat 1).
    
    Example j2 :=
      JSwitch (JConst input2)
              (((Some "v1", CaseType "C1"), (JConst (dstring "1")))
                 :: ((Some "v2", CaseType "C2"), (JConst (dstring "2")))
                 :: nil)
              (JConst (dstring "lots")).

    Definition jc2 := jura_expr_to_calculus ctxt0 j2.
    (* Eval vm_compute in jc2. *)
    (* Eval vm_compute in jlift (fun x => nnrc_eval_top nil x nil) jc2. *)

  End tests.
  
End JuratoJavaScript.

