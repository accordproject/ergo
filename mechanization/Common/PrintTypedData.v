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

Require Import ErgoSpec.Utils.Misc.
Require Import ErgoSpec.Backend.ErgoBackend.
Require Import ErgoSpec.Common.Result.
Require Import ErgoSpec.Common.Names.
Require Import ErgoSpec.Common.Provenance.
Require Import ErgoSpec.Common.NamespaceContext.

Require Import JsAst.JsNumber. (* XXX To be fixed on Q*cert side - JS *)

Local Open Scope string.

Section PrintTypedData.
  Definition print_brand (nsctxt:namespace_ctxt) (b:string) : string :=
    match get_local_part b with
    | None => "~" ++ b
    | Some local_name =>
      elift_both
        (fun resolved_b =>
           if string_dec resolved_b b
           then
             local_name
           else
             "~" ++ b)
        (fun _ => "~" ++ b)
        (resolve_type_name dummy_provenance nsctxt (None,local_name))
    end.

  Definition print_multiple_brands (nsctxt:namespace_ctxt) (bs:list string) : string :=
    "<" ++ (map_concat "," (print_brand nsctxt) bs) ++ ">".
  
  Section Data.
    Context {br:brand_relation}.

    Definition unpack_output
               (out : ergo_data)
      : option (ergo_data * list ergo_data * ergo_data) :=
      match out with
      | (dleft (drec (("__emit", dcoll emits)
                        ::("__response", response)
                        ::("__state", state)
                        ::nil))) =>
        Some (response, emits, state)
      | _ => None
      end.

    Definition fmt_nl := String.String (ascii_of_N 10) EmptyString.
    Definition fmt_dq := """".

    Definition js_quote_char (a:ascii) : string
      := match a with
         | "008"%char => "\b"
         | "009"%char => "\t"
         | "010"%char => "\n"
         | "013"%char => "\r"
         | """"%char => "\"""
         | "\"%char => "\\"
         | _ => (String.String a EmptyString)
         end.

    Definition js_quote_string (s:string) : string
      := flat_map_string js_quote_char s.

    Fixpoint string_of_enum (nsctxt:namespace_ctxt) (d : ergo_data) : string :=
      match d with
      | dleft (dstring x) => x
      | dright d' => string_of_enum nsctxt d'
      | _ => "???should be enum???"
      end.
    
    Fixpoint string_of_data (nsctxt:namespace_ctxt) (d : ergo_data) : string :=
      let jsonify := ErgoData.data_to_json_string fmt_dq in
      let string_of_rec : list (string * ergo_data) -> string :=
          fun rec =>
            ("{"
                ++ (String.concat
                      ", "
                      (map
                         (fun item =>
                            (fst item) ++ ": " ++ (string_of_data nsctxt (snd item)))
                         rec))
                ++ "}") in
      match d with
      | dunit => "unit"
      | dnat z => toString z
      | dfloat f => toString f
      | dbool true => "true"
      | dbool false => "false"
      | dstring s => jsonify (dstring (js_quote_string s))
      | dcoll arr =>
        "["
           ++ (String.concat
                 ", "
                 (map (string_of_data nsctxt) arr))
           ++ "]"
      | dleft s => "some(" ++ (string_of_data nsctxt s) ++ ")"
      | dright _ => "none"
      | dbrand (b::nil) (dleft x) => string_of_enum nsctxt (dleft x)
      | dbrand (b::nil) (dright x) => string_of_enum nsctxt (dright x)
      | dbrand (b::nil) d' => print_brand nsctxt b ++ (string_of_data nsctxt d')
      | dbrand _ _ => "???more than one brand???"
      | drec r => string_of_rec r 
      | dforeign (ErgoEnhancedModel.enhanceddateTimeformat f) =>
        "dateTimeFormat(""" ++ DateTimeModelPart.DATE_TIME_FORMAT_to_string f ++ """)"
      | dforeign (ErgoEnhancedModel.enhanceddateTime dt) =>
        "dateTime(""" ++ DateTimeModelPart.DATE_TIME_format dt (DateTimeModelPart.DATE_TIME_FORMAT_from_string "MM/DD/YYYY") ++ """)"
      | dforeign (ErgoEnhancedModel.enhanceddateTimeduration dti) =>
        "duration(" ++ DateTimeModelPart.DATE_TIME_DURATION_to_string dti ++ ")"
      | dforeign (ErgoEnhancedModel.enhanceddateTimeperiod dti) =>
        "period(" ++ DateTimeModelPart.DATE_TIME_PERIOD_to_string dti ++ ")"
      | dforeign _ => "???UnknownForeign???"
      end.

  End Data.

  Section Types.
    Import ErgoCType.
    
    Context {br:brand_model}.

    Fixpoint rtype_to_string
               (nsctxt:namespace_ctxt) (t : rtype₀) : string :=
      match t with
      | Bottom₀ => "Nothing"
      | Top₀ => "Any"
      | Unit₀ => "Unit"
      | Nat₀ => "Integer"
      | Float₀ => "Double"
      | Bool₀ => "Boolean"
      | String₀ => "String"
      | Coll₀ r' => (rtype_to_string nsctxt r') ++ "[]"
      | Rec₀ k srl =>
        let recend : string :=
            match k with
            | Closed => ""
            | Open => " .."
            end
        in
          "{" ++
             (String.concat
                (", ")
                (map (fun sr => ((fst sr) ++ ": " ++ (rtype_to_string nsctxt (snd sr))))
                     srl)) ++ recend ++ "}"
      | Either₀ tl tr => (rtype_to_string nsctxt tl) ++ "?"
      | Arrow₀ tin tout => (rtype_to_string nsctxt tin) ++ " -> " ++ (rtype_to_string nsctxt tout)
      | Brand₀ (b::nil) => print_brand nsctxt b
      | Brand₀ bs => print_multiple_brands nsctxt bs
      | Foreign₀ ErgoEnhancedModel.enhancedDateTime => "DateTime"
      | Foreign₀ ErgoEnhancedModel.enhancedDateTimeDuration => "InternalDuration"
      | Foreign₀ ErgoEnhancedModel.enhancedDateTimePeriod => "InternalPeriod"
      | Foreign₀ _ => "(unknown foreign type)"
      end.

    Definition ergoc_type_to_string
               (nsctxt:namespace_ctxt) (t : ectype) : string :=
      rtype_to_string nsctxt (ergoc_type_unpack t).

    Definition string_of_result_type
               (nsctxt:namespace_ctxt) (result : option ergoc_type)
      : string :=
      match result with
      | None => ""
      | Some typ => " : " ++ (ergoc_type_to_string nsctxt typ)
      end.

    Definition unpack_error nsctxt kind out :=
      ESystemError dummy_provenance
                   ("Cannot unpack type: "
                      ++ (string_of_result_type nsctxt (Some out))
                      ++ " (expected "
                      ++  kind ++ ")").

    Definition unpack_failure_type
               (nsctxt:namespace_ctxt)
               (out : ergoc_type)
      : eresult ergoc_type :=
      let osuccess :=
          match unteither out with
          | None => None
          | Some (tl, tr) => Some (tl, tr)
          end
      in
      eresult_of_option
        (lift snd osuccess)
        (unpack_error nsctxt "either" out)
        nil.

    Definition unpack_success_type
               (nsctxt:namespace_ctxt)
               (out:ergoc_type)
               (warnings: list ewarning)
      : eresult (ergoc_type * ergoc_type * ergoc_type) :=
      let osuccess :=
          match unteither out with
          | None => None
          | Some (tl, tr) => Some (tl, tr)
          end
      in
      let success :=
          eresult_of_option
            (lift fst osuccess)
            (unpack_error nsctxt "either" out)
            nil
      in
      let response :=
          elift fst
                (eolift
                   (fun success =>
                      (eresult_of_option (ergoc_type_infer_unary_op (OpDot this_response) success)
                                         (unpack_error nsctxt this_response out))
                        nil)
                   success)
      in
      let emit :=
          elift fst
                (eolift
                   (fun success =>
                      (eresult_of_option (ergoc_type_infer_unary_op (OpDot this_emit) success)
                                         (unpack_error nsctxt this_emit out))
                        nil)
                   success)
      in
      let state :=
          elift fst
                (eolift
                   (fun success =>
                      (eresult_of_option (ergoc_type_infer_unary_op (OpDot this_state) success)
                                         (unpack_error nsctxt this_state out))
                        warnings)
                   success)
      in
      elift3 (fun r e s => (r,e,s))
             response emit state.

    Definition unpack_output_type
               (nsctxt:namespace_ctxt)
               (out:ergoc_type)
               (warnings:list ewarning)
      : eresult (ergoc_type * ergoc_type * ergoc_type * ergoc_type) :=
      elift2
        (fun x y =>
           let '(respt,emitt,statet) := x in
           (respt,emitt,statet,y))
        (unpack_success_type nsctxt out warnings)
        (unpack_failure_type nsctxt out).

  End Types.

  Section Both.
    Context {br:brand_model}.

    Definition string_of_response
               (nsctxt:namespace_ctxt)
               (response:ergo_data)
               (response_type:option ergoc_type) : string :=
      "Response. " ++ (string_of_data nsctxt response) ++ (string_of_result_type nsctxt response_type).

    Definition string_of_emits
               (nsctxt:namespace_ctxt)
               (emits:list ergo_data)
               (emit_type:option ergoc_type) : string :=
      match emits with
      | nil => ""
      | e1 :: erest =>
        (fold_right
           (fun new old =>
              (old ++ fmt_nl ++ "Emit. " ++ new))
           ("Emit. " ++ string_of_data nsctxt e1)
           (map (string_of_data nsctxt) erest))
          ++ (string_of_result_type nsctxt emit_type) ++ fmt_nl
      end.

    Definition string_of_state
               (nsctxt:namespace_ctxt)
               (old_state : option ergo_data)
               (new_state : ergo_data)
               (state_type: option ergoc_type)
      : string :=
      let jsonify := string_of_data nsctxt in
      match old_state with
      | None =>  fmt_nl ++ "State. " ++ (jsonify new_state) ++ (string_of_result_type nsctxt state_type)
      | Some actual_old_state =>
        if Data.data_eq_dec new_state actual_old_state
        then ""
        else
          fmt_nl ++ "State. " ++ (jsonify new_state) ++ (string_of_result_type nsctxt state_type)
      end.

    Definition string_of_typed_data
               (nsctxt:namespace_ctxt)
               (old_state : option ergo_data)
               (data: ergo_data)
               (typ: option ergoc_type) : string :=
      match data with
      | dright msg =>
        let failure_type :=
            match typ with
            | None =>  None
            | Some typ => elift_both Some (fun _ => None) (unpack_failure_type nsctxt typ)
            end
        in
        "Failure. " ++ (string_of_data nsctxt msg) ++ (string_of_result_type nsctxt failure_type)
      | out =>
        match unpack_output out with
        | Some (response, emits, state) =>
          let '(response_type, emit_type, state_type) :=
              match typ with
              | None =>  (None, None, None)
              | Some typ =>
                elift_both
                  (fun res => let '(r,e,s) := res in (Some r, Some e, Some s))
                  (fun _ => (None, None, None))
                  (unpack_success_type nsctxt typ nil)
              end
          in
          (string_of_emits nsctxt emits emit_type)
            ++ (string_of_response nsctxt response response_type)
            ++ (string_of_state nsctxt old_state state state_type)
        | None => (string_of_data nsctxt out)
        end
      end.

    Definition string_of_typed_result
               (nsctxt:namespace_ctxt)
               (old_state : option ergo_data)
               (result : option ergoc_type * option ergo_data) : string :=
      match result with
      | (_, None) => ""
      | (typ, Some dat) => (string_of_typed_data nsctxt old_state dat typ) ++ fmt_nl
      end.
  End Both.

End PrintTypedData.

