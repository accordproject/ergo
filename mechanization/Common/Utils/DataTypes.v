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

Require Import Ascii.
Require Import String.
Require Import List.

Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Utils.Misc.
Require Import ErgoSpec.Common.Utils.Result.
Require Import ErgoSpec.Common.Utils.Provenance.
Require Import ErgoSpec.Common.Utils.NamespaceContext.

Require Import JsAst.JsNumber. (* XXX To be fixed on Q*cert side - JS *)

Section DataTypes.
  Definition print_brand (nsctxt:namespace_ctxt) (b:string) : string :=
    match get_local_part b with
    | None => "~"%string ++ b
    | Some local_name =>
      match resolve_type_name dummy_provenance nsctxt.(namespace_ctxt_current) (None,local_name) with
      | Success _ _ resolved_b =>
        if string_dec resolved_b b
        then
          local_name
        else
          "~" ++ b
      | Failure _ _ _ =>
        "~" ++ b
      end
    end.
  
  Section Data.
    Context {br:brand_relation}.

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

    Definition fmt_nl := String.String (ascii_of_N 10) EmptyString.
    Definition fmt_dq := """"%string.

    Fixpoint string_of_data (nsctxt:namespace_ctxt) (d : ergo_data) : string :=
      let jsonify := ErgoData.data_to_json_string fmt_dq in
      let string_of_rec : list (string * ergo_data) -> string :=
          fun rec =>
            ("{"%string
                ++ (String.concat
                      ", "%string
                      (map
                         (fun item =>
                            (fst item) ++ ": " ++ (string_of_data nsctxt (snd item)))
                         rec))
                ++ "}"%string)%string in
      match d with
      | dunit => "nil"%string
      | dnat z => Z_to_string10 z
      | dfloat f => to_string f
      | dbool true => "true"%string
      | dbool false => "false"%string
      | dstring s => jsonify (dstring s)
      | dcoll arr =>
        "["%string
           ++ (String.concat
                 ", "%string
                 (map (string_of_data nsctxt) arr))
           ++ "]"%string
      | dleft s => "some("%string ++ (string_of_data nsctxt s) ++ ")"%string
      | dright _ => "none"
      | dbrand (b::nil) d' => print_brand nsctxt b ++ (string_of_data nsctxt d')
      | dbrand _ _ => "???more than one brand???"%string
      | drec r => string_of_rec r 
      | dforeign _ => "???foreign data???"%string
      end.

    Definition string_of_response (nsctxt:namespace_ctxt) (response : ergo_data) : string :=
      "Response. " ++ (string_of_data nsctxt response) ++ fmt_nl.

    Definition string_of_emits (nsctxt:namespace_ctxt) (emits : list ergo_data) : string :=
      (fold_left
         (fun old new => ("Emit. " ++ new ++ fmt_nl ++ old)%string)
         (map (string_of_data nsctxt) emits) ""%string).

    Definition string_of_state (nsctxt:namespace_ctxt) (old_state : option ergo_data) (new_state : ergo_data)
      : string :=
      let jsonify := string_of_data nsctxt in
      match old_state with
      | None => "State. " ++ (jsonify new_state)
      | Some actual_old_state =>
        if Data.data_eq_dec new_state actual_old_state then
          ""%string
        else
          "State. " ++ (jsonify new_state) ++ fmt_nl
      end.

    Definition string_of_result_data
               (nsctxt:namespace_ctxt) (old_state : option ergo_data) (result : option ergo_data)
      : string :=
      match result with
      | None => ""
      | Some (dright msg) =>
        "Error. "%string ++ (string_of_data nsctxt msg) ++ fmt_nl
      | Some out =>
        match unpack_output out with
        | Some (response, emits, state) =>
          (string_of_emits nsctxt emits)
            ++ (string_of_response nsctxt response)
            ++ (string_of_state nsctxt old_state state)
        | None => (string_of_data nsctxt out) ++ fmt_nl
        end
      end.
  End Data.

  Section Types.
    Import ErgoCTypes.
    
    Context {br:brand_model}.

    Fixpoint rtype_to_string
               (nsctxt:namespace_ctxt) (t : rtype₀) : string :=
      match t with
      | Bottom₀ => "Nothing"%string
      | Top₀ => "Any"%string
      | Unit₀ => "Unit"%string
      | Nat₀ => "Integer"%string
      | Float₀ => "Double"%string
      | Bool₀ => "Boolean"%string
      | String₀ => "String"%string
      | Coll₀ r' => (rtype_to_string nsctxt r') ++ "[]"%string
      | Rec₀ k srl =>
        "{"%string ++
           (String.concat
              (", "%string)
              (map (fun sr => ((fst sr) ++ ": " ++ (rtype_to_string nsctxt (snd sr)))%string)
                   srl)) ++ "}"%string
      | Either₀ tl tr => (rtype_to_string nsctxt tl) ++ "?"%string
      | Arrow₀ tin tout => (rtype_to_string nsctxt tin) ++ " -> "%string ++ (rtype_to_string nsctxt tout)
      | Brand₀ (b::nil) => print_brand nsctxt b
      | Brand₀ _ => "~"%string ++ "[multiple]"
      | Foreign₀ ft => "Foreign (probably DateTime hehe)"
      end.

    Definition ergoc_type_to_string
               (nsctxt:namespace_ctxt) (t : ectype) : string :=
      rtype_to_string nsctxt (ergoc_type_unpack t).

    Definition string_of_result_type
               (nsctxt:namespace_ctxt) (result : option ergoc_type)
      : string :=
      match result with
      | None => ""%string
      | Some typ => "  :  "%string ++ (ergoc_type_to_string nsctxt typ) ++ fmt_nl
      end.

    Definition unpack_type
               (nsctxt:namespace_ctxt)
               (out : ergoc_type)
      : eresult (ergoc_type * ergoc_type * ergoc_type) :=
      let osuccess :=
          match unteither out with
          | None => None
          | Some (tl, _) => Some tl
          end
      in
      let success :=
          eresult_of_option
            osuccess
            (ESystemError dummy_provenance ("CANNOT UNPACK TYPE; Not an either: )"
                                              ++ string_of_result_type nsctxt (Some out)))
      in
      let response :=
          elift fst
                (eolift
                   (fun success =>
                      (eresult_of_option (ergoc_type_infer_unary_op (OpDot "response") success)
                                         (ESystemError dummy_provenance ("CANNOT UNPACK TYPE; No response in: "
                                                                           ++ string_of_result_type nsctxt (Some success)))))
                 success)
      in
      let emit :=
          elift fst
                (eolift
                   (fun success =>
                      (eresult_of_option (ergoc_type_infer_unary_op (OpDot "emit") success)
                                         (ESystemError dummy_provenance ("CANNOT UNPACK TYPE; No emit in: "
                                                                           ++ string_of_result_type nsctxt (Some success)))))
                   success)
      in
      let state :=
          elift fst
                (eolift
                   (fun success =>
                      (eresult_of_option (ergoc_type_infer_unary_op (OpDot "state") success)
                                         (ESystemError dummy_provenance ("CANNOT UNPACK TYPE; No state in: "
                                                                           ++ string_of_result_type nsctxt (Some success)))))
                   success)
      in
      elift3 (fun r e s => (r,e,s))
             response emit state.
  End Types.

  Section Both.
    Context {br:brand_model}.

    Definition string_of_result
               (nsctxt:namespace_ctxt)
               (old_state : option ergo_data)
               (result : (option ergoc_type * option ergo_data)) : string :=
      match result with
      | (typ, dat) => (string_of_result_data nsctxt old_state dat) ++ (string_of_result_type nsctxt typ)
      end.
  End Both.

End DataTypes.

