(*
 * Copyright 2015-2016 IBM Corporation
 *
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

Require Import List.
Require Import Ascii.
Require Import String.
Require Import ZArith.
Require Import JsAst.JsNumber.

Require Import Qcert.Utils.Utils.

Require Import ErgoSpec.Utils.Misc.

Section EJSON.
  Unset Elimination Schemes.

  Inductive ejson : Set :=
  | ejnull : ejson
  | ejnumber : number -> ejson
  | ejbool : bool -> ejson
  | ejstring : estring -> ejson
  | ejarray : list ejson -> ejson
  | ejobject : list (estring * ejson) -> ejson
  .

  Set Elimination Schemes.

  (** Induction principles used as backbone for inductive proofs on ejson *)
  Definition ejson_rect (P : ejson -> Type)
             (fnull : P ejnull)
             (fnumber : forall n : number, P (ejnumber n))
             (fbool : forall b : bool, P (ejbool b))
             (fstring : forall s : estring, P (ejstring s))
             (farray : forall c : list ejson, Forallt P c -> P (ejarray c))
             (fobject : forall r : list (estring * ejson), Forallt (fun ab => P (snd ab)) r -> P (ejobject r))
    :=
      fix F (j : ejson) : P j :=
    match j as j0 return (P j0) with
      | ejnull => fnull
      | ejnumber x => fnumber x
      | ejbool x => fbool x
      | ejstring x => fstring x
      | ejarray x => farray x ((fix F2 (c : list ejson) : Forallt P c :=
                            match c as c0 with
                              | nil => Forallt_nil _
                              | cons j c0 => @Forallt_cons _ P j c0 (F j) (F2 c0)
                            end) x)
      | ejobject x => fobject x ((fix F3 (r : list (estring*ejson)) : Forallt (fun ab => P (snd ab)) r :=
                           match r as c0 with
                             | nil => Forallt_nil _
                             | cons sj c0 => @Forallt_cons _ (fun ab => P (snd ab)) sj c0 (F (snd sj)) (F3 c0)
                           end) x)
    end.

  Definition ejson_ind (P : ejson -> Prop)
             (fnull : P ejnull)
             (fnumber : forall n : number, P (ejnumber n))
             (fbool : forall b : bool, P (ejbool b))
             (fstring : forall s : estring, P (ejstring s))
             (farray : forall c : list ejson, Forall P c -> P (ejarray c))
             (fobject : forall r : list (estring * ejson), Forall (fun ab => P (snd ab)) r -> P (ejobject r))
    :=
      fix F (j : ejson) : P j :=
    match j as j0 return (P j0) with
      | ejnull => fnull
      | ejnumber x => fnumber x
      | ejbool x => fbool x
      | ejstring x => fstring x
      | ejarray x => farray x ((fix F2 (c : list ejson) : Forall P c :=
                            match c with
                              | nil => Forall_nil _
                              | cons j c0 => @Forall_cons _ P j c0 (F j) (F2 c0)
                            end) x)
      | ejobject x => fobject x ((fix F3 (r : list (estring*ejson)) : Forall (fun ab => P (snd ab)) r :=
                           match r with
                             | nil => Forall_nil _
                             | cons sj c0 => @Forall_cons _ (fun ab => P (snd ab)) sj c0 (F (snd sj)) (F3 c0)
                           end) x)
    end.

  Definition ejson_rec (P:ejson->Set) := ejson_rect P.
  
  Lemma ejsonInd2 (P : ejson -> Prop)
        (f : P ejnull)
        (f0 : forall n : number, P (ejnumber n))
        (fb : forall b : bool, P (ejbool b))
        (f1 : forall s : estring, P (ejstring s))
        (f2 : forall c : list ejson, (forall x, In x c -> P x) -> P (ejarray c))
        (f3 : forall r : list (estring * ejson), (forall x y, In (x,y) r -> P y) -> P (ejobject r)):
    forall d, P d.
  Proof.
    intros.
    apply ejson_ind; trivial.
    - intros. rewrite Forall_forall in H.
      auto.
    - intros. rewrite Forall_forall in H.
      apply f3.
      intros. apply (H (x,y)). trivial.
  Qed.

  Section toString.

    Local Open Scope estring_scope.

    Definition js_quote_char (a:ascii) : estring
      := match a with
         | """"%char => `"\"""
         | _ => (`String a EmptyString)
         end.

    Definition js_quote_string (s:estring)
      := flat_map_estring js_quote_char s.

    Definition stringToJS (quotel:string) (s:estring)
      := `"" +++ `quotel +++ `"" +++ js_quote_string s +++ `"" +++ `quotel +++ `"".

    Fixpoint ejsonToJS (quotel:string) (j : ejson) : estring
      := match j with
         | ejnull => `"null" (* to be discussed *)
         | ejnumber n => `to_string n
         | ejbool b => if b then `"true" else `"false"
         | ejstring s => stringToJS quotel s
         | ejarray ls =>
           let ss := map (ejsonToJS quotel) ls in
           `"[" +++ (econcat (`", ") ss) +++ `"]"
         | ejobject ls =>
           let ss := (map (fun kv => let '(k,v) := kv in
                                     `"" +++ `quotel +++ `"" +++ k +++ `"" +++ `quotel +++ `": " +++ (ejsonToJS quotel v)) ls) in
           `"{" +++ (econcat (`", ") ss) +++ `"}"
         end.

    Fixpoint json_to_ejson (j:json) : ejson :=
      match j with
      | jnil => ejnull
      | jnumber n => ejnumber n
      | jbool b => ejbool b
      | jstring s => ejstring (`s)
      | jarray ls =>
        ejarray (map json_to_ejson ls)
      | jobject ls =>
        ejobject (map (fun kv => let '(k,v) := kv in
                                 (`k, json_to_ejson v)) ls)
      end.
    
  End toString.
  
End EJSON.

