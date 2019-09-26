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

Require Import List.
Require Import String.
Require Import Ascii.
Require Import Peano_dec.
Require Import EquivDec.
Require Import Qcert.Utils.Utils.
Require Import Qcert.Common.CommonRuntime.
Require Import Qcert.NNRC.NNRCRuntime.
Require Import Qcert.JavaScript.JavaScriptRuntime.
Require Import Qcert.Translation.ForeignToJavaScript.

Require Import ErgoSpec.Utils.EJSON.
Require Import ErgoSpec.Utils.Misc.

Local Open Scope string_scope.

Section ENNRCtoJavaScript.

  Context {fruntime:foreign_runtime}.
  Context {ftojavascript:foreign_to_javascript}.
  Context {ftjson:foreign_to_JSON}.

  Section global_rename.
    (* Java equivalent: NnnrcOptimizer.unshadow *)

    Definition varmap : Set := list (string*string).

    Definition picknewvar (x:string) (vm:varmap) : (string * varmap) :=
      match lookup string_dec vm x with
      | None => (x,(x,x)::vm)
      | Some _ =>
        let x' := fresh_var_from "$" x (List.map snd vm) in
        (x',(x,x')::vm)
      end.
  
    Fixpoint rename (vm:varmap) (e:nnrc) : (nnrc * varmap) :=
      match e with
      | NNRCGetConstant x => (NNRCGetConstant x, vm)
      | NNRCVar x =>
        (* lookup in varmap for new name *)
        match lookup string_dec vm x with
        | Some x' => (NNRCVar x', vm)
        | None => (NNRCVar x, vm)
        end
      | NNRCConst d =>
        (NNRCConst d, vm)
      | NNRCBinop bop e1 e2 =>
        let (e1',vm1) := rename vm e1 in
        let (e2',vm2) := rename vm1 e2 in
        (NNRCBinop bop e1' e2', vm2)
      | NNRCUnop uop e1 =>
        let (e1',vm1) := rename vm e1 in
        (NNRCUnop uop e1', vm1)
      | NNRCLet x e1 e2 =>
        let (e1',vm1) := rename vm e1 in
        let (x',vm1') := picknewvar x vm1 in
        let (e2',vm2) := rename vm1' e2 in
        (NNRCLet x' e1' e2',vm2)
      | NNRCFor x e1 e2 => 
        let (e1',vm1) := rename vm e1 in
        let (x',vm1') := picknewvar x vm1 in
        let (e2',vm2) := rename vm1' e2 in
        (NNRCFor x' e1' e2',vm2)
      | NNRCIf e1 e2 e3 =>
        let (e1',vm1) := rename vm e1 in
        let (e2',vm2) := rename vm1 e2 in
        let (e3',vm3) := rename vm2 e3 in
        (NNRCIf e1' e2' e3', vm3)
      | NNRCEither ed xl el xr er =>
        let (ed',vmd) := rename vm ed in
        let (xl',vml) := picknewvar xl vmd in
        let (el',vml') := rename vml el in
        let (xr',vmr) := picknewvar xr vml' in
        let (er',vmr') := rename vmr er in
        (NNRCEither ed' xl' el' xr' er', vmr')
      | NNRCGroupBy g sl e1 =>
        let (e1',vm1) := rename vm e1 in
        (NNRCGroupBy g sl e1', vm1)
      end.

    Definition rename_top (e:nnrc) : nnrc :=
      fst (coq_time "nnrc(rename)" (rename nil) e).
  End global_rename.

Section sanitizer.
  Import ListNotations.
  
  (* javascript allows identifiers that begin with a unicode letter, underscore, or dollar sign.
         We avoid beginning with an underscore or dollar sign to 
         avoid problems with frameworks/libraries.
         Since Coq does not seem to have a unicode library, 
         we just allow ascii characters.
   *)

  Definition jsAllowedIdentifierInitialCharacters := ["A";"B";"C";"D";"E";"F";"G";"H";"I";"J";"K";"L";"M";"N";"O";"P";"Q";"R";"S";"T";"U";"V";"W";"X";"Y";"Z";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z"]%char.

  (* javascript identifiers can have (after the first character), a unicode letter, digit, underscore, or dollar sign.
         Since Coq does not seem to have a unicode library, we just
         allow ascii characters,
   *)
  Definition jsAllowedIdentifierCharacters := ["A";"B";"C";"D";"E";"F";"G";"H";"I";"J";"K";"L";"M";"N";"O";"P";"Q";"R";"S";"T";"U";"V";"W";"X";"Y";"Z";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z";"0";"1";"2";"3";"4";"5";"6";"7";"8";"9";"_";"$"]%char.

  Definition jsIdentifierInitialCharacterToAdd := "X"%char.
  Definition jsIdenitiferCharacterForReplacement := "X"%char.

  Definition jsIdentifierFixInitial (ident:string) : string
    := match ident with
       (* We also don't want empty identifier names *)
       | EmptyString =>
         String jsIdentifierInitialCharacterToAdd EmptyString
       | String a _ =>
         if in_dec ascii_dec a jsAllowedIdentifierInitialCharacters
         then ident
         else String jsIdentifierInitialCharacterToAdd ident
       end.

  Definition jsIdentifierSanitizeChar (a:ascii)
    := if in_dec ascii_dec a jsAllowedIdentifierCharacters
       then a
       else jsIdenitiferCharacterForReplacement.

  Definition jsIdentifierSanitizeBody (ident:string)
    := map_string jsIdentifierSanitizeChar ident.

  (* Java equivalent: JavaScriptBackend.jsIdentifierSanitize *)  
  Definition jsIdentifierSanitize (ident:string)
    := jsIdentifierFixInitial (jsIdentifierSanitizeBody ident).

  Definition jsSafeSeparator := "_".

  (* pulled of off various lists of javascript reserved keywords 
         as well some common html/java words that should be avoided
          in case of shared context/interop *)
  Definition jsAvoidList :=
    ["Array"; "Date"; "Infinity"; "JavaArray"; "JavaObject"; "JavaPackage"
     ; "Math"; "NaN"; "Number"; "Object"; "String"
     ; "abstract"; "alert" ; "all"; "anchor"; "anchors"; "area"; "arguments"
     ; "assign"; "await"
     ; "blur"; "boolean"; "break"; "button"; "byte"
     ; "case"; "catch"; "char"; "checkbox"; "class"; "clearInterval"
     ; "clearTimeout"; "clientInformation"; "close"; "closed"; "confirm"
     ; "const"; "constructor"; "continue"; "crypto"
     ; "debugger"; "decodeURI"; "decodeURIComponent"; "default"
     ; "defaultStatus"; "delete"; "do"; "document"; "double"
     ; "element"; "elements"; "else"; "embed"; "embeds"; "encodeURI"
     ; "encodeURIComponent"; "enum"; "escape"; "eval"; "eval"; "event"
     ; "export"; "extends"
     ; "false"; "fileUpload"; "final"; "finally"; "float"; "focus"; "for"
     ; "form"; "forms"; "frame"; "frameRate"; "frames"; "function"; "function"
     ; "getClass"; "goto"
     ; "hasOwnProperty"; "hidden"; "history"
     ; "if"; "image"; "images"; "implements"; "import"; "in"; "innerHeight"
     ; "innerWidth"; "instanceof"; "int"; "interface"; "isFinite"; "isNaN"
     ; "isPrototypeOf"
     ; "java"; "javaClass"
     ; "layer"; "layers"; "length"; "let"; "link"; "location"; "long"
     ; "mimeTypes"
     ; "name"; "native"; "navigate"; "navigator"; "new"; "null"
     ; "offscreenBuffering"; "open"; "opener"; "option"; "outerHeight"
     ; "outerWidth"
     ; "package"; "packages"; "pageXOffset"; "pageYOffset"; "parent"
     ; "parseFloat"; "parseInt"; "password"; "pkcs11"; "plugin"; "private"
     ; "prompt"; "propertyIsEnum"; "protected"; "prototype"; "public"
     ; "radio"; "reset"; "return"
     ; "screenX"; "screenY"; "scroll"; "secure"; "select"; "self"
     ; "setInterval"; "setTimeout"; "short"; "static"; "status"
     ; "submit"; "super"; "switch"; "synchronized"
     ; "taint"; "text"; "textarea"; "this"; "throw"; "throws"; "toString"
     ; "top"; "transient"; "true"; "try"; "typeof"
     ; "undefined"; "unescape"; "untaint"
     ; "valueOf"; "var"; "void"; "volatile"
     ; "while"; "window"; "with"
     ; "yield"].

  (* Java equivalent: JavaScriptBackend.unshadow_js *)
  Definition unshadow_js (avoid:list var) (e:nnrc) : nnrc
    := rename_top (unshadow jsSafeSeparator jsIdentifierSanitize (avoid++jsAvoidList) e).

End sanitizer.

  Definition varvalue := 100.
  Definition varenv := 1.

  Section JSUtil.
    Local Open Scope estring_scope.

    Definition eol_newline : estring  := ` (String (Ascii.ascii_of_nat 10) EmptyString).
    Definition eol_backn : estring := `"\n".

    Definition quotel_double : estring := `"""".
    Definition quotel_backdouble  : estring := `"\""".
    
    (* Java equivalent: JavaScriptBackend.indent *)
    Fixpoint indent (i : nat) : estring
      := match i with
         | 0 => `""
         | S j => `"  " +++ (indent j)
         end.

  End JSUtil.

  Section DataJS.
    Local Open Scope estring_scope.

    Definition bracketString (open s close:string) : string
      := append open (append s close).

    (* Java equivalent: JavaScriptBackend.brandsToJS *)
    Definition brandsToJs (quotel:estring) (b:brands) : estring
      := ` (bracketString "[" (map_concat "," (fun x => bracketString (^quotel) x (^quotel)) b) "]").

    Fixpoint data_to_js (d:data) : ejson :=
      match d with
      | dunit =>
        ejnull
      | dnat n =>
        ejobject ((`"nat"%string, ejnumber (float_of_int n))::nil)
      | dfloat n =>
        ejnumber n
      | dbool b =>
        ejbool b
      | dstring s =>
        ejstring (`s)
      | dcoll c =>
        ejarray (map data_to_js c)
      | drec r =>
        ejobject (map (fun x => (`fst x, data_to_js (snd x))) r)
      | dleft d' =>
        ejobject ((`"left"%string, data_to_js d')::nil)
      | dright d' =>
        ejobject ((`"right"%string, data_to_js d')::nil)
      | dbrand b d' =>
        ejobject ((`"type"%string, ejarray (map (fun s => ejstring (`s)) b))::(`"data"%string, (data_to_js d'))::nil)
      | dforeign fd => json_to_ejson (foreign_to_JSON_from_data fd)
      end.

    Fixpoint data_to_json (d:data) : ejson := data_to_js d.
    
    (* Java equivalent: JavaScriptBackend.dataToJS *)
    Definition dataToJS (quotel:estring) (d : data) : estring :=
      ejsonToJS (^quotel) (data_to_js d).

    Definition inheritanceToJS (quotel:estring) (h:list (string*string)) :estring :=
      `(dataToJS quotel (dcoll (map (fun x => drec (("sub",dstring (fst x)) :: ("sup", (dstring (snd x))) :: nil)) h))).

  End DataJS.

  Section NNRCJS.
    Local Open Scope estring_scope.

    (* Sort criteria *)
    Definition singleSortCriteriaToJson (sc: string * SortDesc) : json :=
      match snd sc with
      | Ascending => jobject (("asc", jstring (fst sc))::nil)
      | Descending => jobject (("desc", jstring (fst sc))::nil)
      end.

    Definition sortCriteriaToJson (scl:SortCriterias) : json
      := jarray (map singleSortCriteriaToJson scl).

    Definition sortCriteriaToJs (quotel:estring) (scl:SortCriterias) : estring
      := `  (jsonToJS (^ quotel) (sortCriteriaToJson scl)).
    
    (* Java equivalent: JavaScriptBackend.uarithToJS *)
    Definition uarithToJs (u:nat_arith_unary_op) (e:estring) : estring :=
      match u with
      | NatAbs => `"natAbs(" +++ e +++ `")"
      | NatLog2 => `"natLog2(" +++ e +++ `")"
      | NatSqrt => `"natSqrt(" +++ e +++ `")"
      end.

    Definition float_uarithToJs (fu:float_arith_unary_op) (d:estring) : estring :=
      match fu with
      | FloatNeg => `"-" +++ `"(" +++ d +++ `")"
      | FloatSqrt => `"Math.sqrt(" +++ `"-" +++ d +++ `")"
      | FloatExp => `"Math.exp(" +++ d +++ `")" 
      | FloatLog => `"Math.log2(" +++ d +++ `")"
      | FloatLog10 => `"Math.log10(" +++ d +++ `")"
      | FloatCeil => `"Math.ceil(" +++ d +++ `")" 
      | FloatFloor => `"Math.floor(" +++ d +++ `")" 
      | FloatAbs => `"Math.abs(" +++ d +++ `")"
      end.

    (* Java equivalent: JavaScriptBackend.barithToJs *)
    Definition nat_barithToJs (b:nat_arith_binary_op) (e1 e2:estring) : estring :=
      match b with
      | NatPlus => `"natPlus(" +++ e1 +++ `", " +++ e2 +++ `")"
      | NatMinus => `"natMinus(" +++ e1 +++ `", " +++ e2 +++ `")"
      | NatMult => `"natMult(" +++ e1 +++ `", " +++ e2 +++ `")"
      | NatDiv => `"natDiv(" +++ e1 +++ `", " +++ e2 +++ `")"
      | NatRem => `"natRem(" +++ e1 +++ `", " +++ e2 +++ `")"
      | NatMin => `"natMin(" +++ e1 +++ `", " +++ e2 +++ `")"
      | NatMax => `"natMax(" +++ e1 +++ `", " +++ e2 +++ `")"
      end.
    
    Definition mumber_barithToJs (fb:float_arith_binary_op) (d1 d2:estring) : estring :=
      match fb with
      | FloatPlus => `"(" +++ d1 +++ `" + " +++ d2 +++ `")"
      | FloatMinus =>  `"(" +++ d1 +++ `" - " +++ d2 +++ `")"
      | FloatMult =>  `"(" +++ d1 +++ `" * " +++ d2 +++ `")"
      | FloatDiv =>  `"(" +++ d1 +++ `" / " +++ d2 +++ `")"
      | FloatPow => `"Math.pow(" +++ d1 +++ `", " +++ d2 +++ `")"
      | FloatMin => `"Math.min(" +++ d1 +++ `", " +++ d2 +++ `")"
      | FloatMax => `"Math.max(" +++ d1 +++ `", " +++ d2 +++ `")"
      end.

    Definition mumber_bcompareToJs (fb:float_compare_binary_op) (d1 d2:estring) : estring :=
      match fb with
      | FloatLt => `"(" +++ d1 +++ `" < " +++ d2 +++ `")"
      | FloatLe => `"(" +++ d1 +++ `" <= " +++ d2 +++ `")"
      | FloatGt => `"(" +++ d1 +++ `" > " +++ d2 +++ `")"
      | FloatGe => `"(" +++ d1 +++ `" >= " +++ d2 +++ `")"
      end.

    Definition like_clause_to_javascript (lc:like_clause) : string
      := match lc with
         | like_literal literal => "escapeRegExp(" ++ ^quotel_double ++ literal ++ ^quotel_double ++ ")"
         | like_any_char => ^quotel_double ++ "." ++ ^quotel_double 
         | like_any_string => ^quotel_double ++ ".*" ++ ^quotel_double 
         end.

    (* Java equivalent: JavaScript.Backend.nrcToJS *)
    Fixpoint nnrcToJS
             (n : nnrc)                      (* NNRC expression to translate *)
             (t : nat)                       (* next available unused temporary *)
             (i : nat)                       (* indentation level *)
             (eol : estring)                  (* Choice of end of line character *)
             (quotel : estring)               (* Choice of quote character *)
             (ivs : list (string * string))  (* Input variables and their corresponding string representation *)
      : ejavascript                           (* JavaScript statements for computing result *)
        * ejavascript                         (* JavaScript expression holding result *)
        * nat                                (* next available unused temporary *)
      := match n with
         | NNRCGetConstant v => (`"", `"" +++ `v, t)
         | NNRCVar v =>
           match assoc_lookupr equiv_dec ivs v with
           | Some v_string => (`"", `v_string, t)
           | None => (`"", `"v" +++ `v, t)
           end
         | NNRCConst d => (`"", dataToJS quotel d, t)
         | NNRCUnop op n1 =>
           let '(s1, e1, t0) := nnrcToJS n1 t i eol quotel ivs in
           let e0 := match op with
                     | OpIdentity => e1
                     | OpNeg => `"!(" +++ e1 +++ `")"
                     | OpRec s => `"{" +++ quotel +++ `s +++ quotel +++ `": " +++ e1 +++ `"}"
                     | OpDot s => `"deref(" +++ e1 +++ `", " +++ quotel +++ `s  +++ quotel +++ `")"
                     | OpRecRemove s => `"remove(" +++ e1 +++ `", " +++ quotel +++ `"" +++ `s +++ `"" +++ quotel +++ `")"
                     | OpRecProject sl => `"project(" +++ e1 +++ `", " +++ (brandsToJs quotel sl) +++ `")"
                     | OpBag => `"[" +++ e1 +++ `"]"
                     | OpSingleton => `"singleton(" +++ e1 +++ `")"
                     | OpFlatten => `"flatten(" +++ e1 +++ `")"
                     | OpDistinct => `"distinct(" +++ e1 +++ `")"
                     | OpOrderBy scl => `"sort(" +++ e1 +++ `", " +++ (sortCriteriaToJs quotel scl) +++ `")"
                     | OpCount => `"count(" +++ e1 +++ `")"
                     | OpToString => `"toString(" +++ e1 +++ `")"
                     | OpGenerateText => `"generateText(" +++ e1 +++ `")"
                     | OpLength => `"stringLength(" +++ e1 +++ `")"
                     | OpSubstring start olen =>
                       match olen with
                       | None =>
                         `"substringNoLength(" +++ e1 +++ `"," +++ `toString start +++ `")"
                       | Some len =>
                         `"substring(" +++ e1 +++ `"," +++ `toString start +++ `"," +++ `toString len +++ `")"
                       end
                     | OpLike pat oescape =>
                       let lc := make_like_clause pat oescape in
                       let regex := `"new RegExp([" +++ ` (map_concat "," like_clause_to_javascript lc) +++ `"].join(" +++ quotel +++ quotel +++ `"))" in
                       regex +++ `".test(" +++ e1 +++ `")"
                     | OpLeft => `"{" +++ quotel +++ `"left" +++ quotel +++ `" : " +++ e1 +++ `"}"
                     | OpRight => `"{" +++ quotel +++ `"right" +++ quotel +++ `" : " +++ e1 +++ `"}"
                     | OpBrand b => `"brand(" +++ brandsToJs quotel b +++ `"," +++ e1 +++ `")"
                     | OpUnbrand => `"unbrand(" +++ e1 +++ `")"
                     | OpCast b => `"cast(" +++ brandsToJs quotel b +++ `"," +++ e1 +++ `")"
                     | OpNatUnary u => uarithToJs u e1
                     | OpNatSum => `"natSum(" +++ e1 +++ `")"
                     | OpNatMin => `"natMinApply(" +++ e1 +++ `")"
                     | OpNatMax => `"natMaxApply(" +++ e1 +++ `")"
                     | OpNatMean => `"natArithMean(" +++ e1 +++ `")"
                     | OpFloatOfNat => `"floatOfNat(" +++ e1 +++ `")"
                     | OpFloatUnary u => float_uarithToJs u e1
                     | OpFloatTruncate => `"natBox(Math.trunc(" +++ e1 +++ `"))" 
                     | OpFloatSum => `"sum(" +++ e1 +++ `")"
                     | OpFloatMean => `"arithMean(" +++ e1 +++ `")"
                     | OpFloatBagMin => `"Math.min.apply(Math," +++ e1 +++ `")"
                     | OpFloatBagMax => `"Math.max.apply(Math," +++ e1 +++ `")"
                     | OpForeignUnary fu
                       => ` (foreign_to_javascript_unary_op i (^eol) (^quotel) fu (^e1))
                     end in
           (s1, e0, t0)
         | NNRCBinop op n1 n2 =>
           let '(s1, e1, t2) := nnrcToJS n1 t i eol quotel ivs in
           let '(s2, e2, t0) := nnrcToJS n2 t2 i eol quotel ivs in
           let e0 := match op with
                     | OpEqual => `"equal(" +++ e1 +++ `", " +++ e2 +++ `")"
                     | OpRecConcat => `"concat(" +++ e1 +++ `", " +++ e2 +++ `")"
                     | OpRecMerge => `"mergeConcat(" +++ e1 +++ `", " +++ e2 +++ `")"
                     | OpAnd => `"(" +++ e1 +++ `" && " +++ e2 +++ `")"
                     | OpOr => `"(" +++ e1 +++ `" || " +++ e2 +++ `")"
                     | OpLt => `"(compare(" +++ e1 +++ `"," +++ e2 +++ `") < 0)" (* XXX Use compare! *)
                     | OpLe => `"(compare(" +++ e1 +++ `"," +++ e2 +++ `") <= 0)" (* XXX Use compare! *)
                     | OpBagUnion => `"bunion(" +++ e1 +++ `", " +++ e2 +++ `")"
                     | OpBagDiff => `"bminus(" +++ e1 +++ `", " +++ e2 +++ `")"
                     | OpBagMin => `"bmin(" +++ e1 +++ `", " +++ e2 +++ `")"
                     | OpBagMax => `"bmax(" +++ e1 +++ `", " +++ e2 +++ `")"
                     | OpBagNth => `"bnth(" +++ e1 +++ `", " +++ e2 +++ `")"
                     | OpContains => `"contains(" +++ e1 +++ `", " +++ e2 +++ `")"
                     | OpStringConcat => `"(" +++ e1 +++ `" + " +++ e2 +++ `")"
                     | OpStringJoin => `"stringJoin(" +++ e1 +++ `", " +++ e2 +++ `")"
                     | OpNatBinary b => nat_barithToJs b e1 e2
                     | OpFloatBinary b => mumber_barithToJs b e1 e2
                     | OpFloatCompare b => mumber_bcompareToJs b e1 e2
                     | OpForeignBinary fb
                       => ` (foreign_to_javascript_binary_op i (^eol) (^quotel) fb (^e1) (^e2))
                     end in
           (s1 +++ s2, e0, t0)
         | NNRCLet v bind body =>
           let '(s1, e1, t2) := nnrcToJS bind t i eol quotel ivs in
           let '(s2, e2, t0) := nnrcToJS body t2 i eol quotel ivs in
           let v0 := `"v" +++ `v in
           (s1 +++ (indent i) +++ `"var " +++ v0 +++ `" = " +++ e1 +++ `";" +++ eol
               +++ s2,
            e2, t0)
         | NNRCFor v iter body =>
           let '(s1, e1, t2) := nnrcToJS iter t i eol quotel ivs in
           let '(s2, e2, t0) := nnrcToJS body t2 (i+1) eol quotel ivs in
           let elm := `"v" +++ `v in
           let src := `"src" +++ ` (nat_to_string10 t0) in
           let idx := `"i" +++ `  (nat_to_string10 t0) in
           let dst := `"dst" +++ ` (nat_to_string10 t0) in
           (s1 +++ (indent i) +++ `"var " +++ dst +++ `" = [];" +++ eol
               +++ (indent i) +++ (`"for (var "
                                   +++ src +++ `"=" +++ e1 +++ `", "
                                   +++ idx +++ `"=0; "
                                   +++ idx +++ `"<" +++ src +++ `".length; "
                                   +++ idx +++ `"++) {" +++ eol)
               +++ (indent (i+1)) +++ (`"var " +++ elm +++ `" = " +++ src
                                               +++ `"[" +++ idx +++ `"];" +++ eol)
               +++ s2
               +++ (indent (i+1)) +++ dst +++ `".push(" +++ e2 +++ `");" +++ eol
               +++ (indent i) +++ `"}" +++ eol,
            dst, t0 + 1)
         | NNRCIf c n1 n2 =>
           let '(s1, e1, t2) := nnrcToJS c t i eol quotel ivs in
           let '(s2, e2, t3) := nnrcToJS n1 t2 (i+1) eol quotel ivs in
           let '(s3, e3, t0) := nnrcToJS n2 t3 (i+1) eol quotel ivs in
           let v0 := `"t" +++ ` (nat_to_string10 t0) in
           (s1 +++ (indent i) +++ `"var " +++ v0 +++ `";" +++ eol
               +++ (indent i) +++ `"if (" +++ e1 +++ `") {" +++ eol
               +++ s2
               +++ (indent (i+1)) +++ v0 +++ `" = " +++ e2 +++ `";" +++ eol
               +++ (indent i) +++ `"} else {" +++ eol
               +++ s3
               +++ (indent (i+1)) +++ v0 +++ `" = " +++ e3 +++ `";" +++ eol
               +++ (indent i) +++ `"}" +++ eol,
            v0, t0 + 1)
         | NNRCEither nd xl nl xr nr =>
           let '(s1, e1, t2) := nnrcToJS nd t i eol quotel ivs in
           let '(s2, e2, t0) := nnrcToJS nl t2 (i+1) eol quotel ivs in
           let '(s3, e3, t1) := nnrcToJS nr t0 (i+1) eol quotel ivs in
           let vl := `"v" +++ `xl in
           let vr := `"v" +++ `xr in
           let res := `"res" +++ ` (nat_to_string10 t1) in  (* Stores the result from either left or right evaluation so it can be returned *)
           (s1 +++ (indent i) +++ `"var " +++ res +++ `" = null;" +++ eol
               +++ (indent i) +++ `"if (either(" +++ e1 +++ `")) {" +++ eol
               +++ (indent (i+1)) +++ `"var " +++ vl +++ `" = null;" +++ eol
               +++ (indent (i+1)) +++ vl +++ `" = toLeft(" +++ e1 +++ `");" +++ eol
               +++ s2
               +++ (indent (i+1)) +++ res +++ `" = " +++ e2 +++ `";" +++ eol
               +++ (indent i) +++ `"} else {" +++ eol
               +++ (indent (i+1)) +++ `"var " +++ vr +++ `" = null;" +++ eol
               +++ (indent (i+1)) +++ vr +++ `" = toRight(" +++ e1 +++ `");" +++ eol
               +++ s3
               +++ (indent (i+1)) +++ res +++ `" = " +++ e3 +++ `";" +++ eol
               +++ (indent i) +++ `"}" +++ eol,
            res, t1 + 1)
         | NNRCGroupBy g sl n1 =>
           let '(s1, e1, t0) := nnrcToJS n1 t i eol quotel ivs in
           let e0 := `"groupby(" +++ e1 +++ `", "
                                +++ quotel +++ `g +++ quotel +++ `", "
                                +++ (brandsToJs quotel sl) +++ `")" in
           (s1, e0, t0)
       end.

    (* Java equivalent: JavaScriptBackend.nrcToJSunshadow *)
    Definition nnrcToJSunshadow
               (n : nnrc)
               (t : nat)
               (i : nat)
               (eol : estring)
               (quotel : estring)
               (avoid: list var)
               (ivs : list (string * string))
      := let n := unshadow_js avoid n in
         nnrcToJS n t i eol quotel ivs.

    (* Java equivalent: JavaScriptBackend.makeJSParams *)
    Definition makeJSParams (ivs: list string)  : estring :=
      ` (concat ", " ivs).

    (* Java equivalent: JavaScriptBackend.paramsToStringedParams *)
    Definition paramsToStringedParams (params : list string) :=
      map (fun x => (x,x)) params.

    (* Java equivalent: JavaScriptBackend.nrcToJSFunStub *)    
    Definition nnrcToJSFunStub
               (e:nnrc)
               (harness:bool)
               (i:nat)
               (eol:estring)
               (quotel:estring)
               (params : list string)
               (fname:string)
      := let '(j0, v0, t0) := nnrcToJSunshadow e 1 (i+1) eol quotel params (paramsToStringedParams params) in
         `"" +++ (indent i) +++ `"function " +++ `fname +++ `"(" +++ (makeJSParams params) +++ `") {" +++ eol
             +++ j0
             +++ (indent i) +++ `"  return " +++ v0 +++ `";" +++ eol
             +++ (indent i) +++ `"}" +++ eol
             +++ (if harness then `"%HARNESS%" else `"").

    Definition nnrcToJSFunStubConstants
               (e:nnrc)
               (i:nat)
               (eol:estring)
               (quotel:estring)
               (params : list string)
               (fname:string)
               (fprefix:string)
      := let '(j0, v0, t0) := nnrcToJSunshadow e 1 (i+1) eol quotel params (paramsToStringedParams params) in
         `"" +++ (indent i) +++ `fprefix +++ `fname +++ `"(" +++ (makeJSParams params) +++ `") {" +++ eol
             +++ j0
             +++ (indent i) +++ `"  return " +++ v0 +++ `";" +++ eol
             +++ (indent i) +++ `"}".

    (* Java equivalent: JavaScriptBackend.nrcToJSFunStubConstants *)
    Definition nnrcToJSFunStubConstantsAsFunction
               (e:nnrc)
               (i:nat)
               (eol:estring)
               (quotel:estring)
               (params : list string)
               (fname:string)
      := let fprefix := "function " in
         nnrcToJSFunStubConstants e i eol quotel params fname fprefix.

    Definition nnrcToJSFunStubConstantsAsMethod
               (e:nnrc)
               (i:nat)
               (eol:estring)
               (quotel:estring)
               (params : list string)
               (fname:string)
      := let fprefix := "" in
         nnrcToJSFunStubConstants e i eol quotel params fname fprefix.

    (* Java equivalent: JavaScriptBackend.nrcToJSFun *)
    Definition nnrcToJSFun
               (input_v:string)
               (e:nnrc)
               (i:nat)
               (eol:estring)
               (quotel:estring)
               (ivs : list string)
               (fname:string)
      := let e' := closeFreeVars jsSafeSeparator jsIdentifierSanitize (NNRCVar input_v) e ivs in
         nnrcToJSFunStubConstantsAsFunction e' i eol quotel ivs fname.

    Definition nnrcToJSMethod
               (input_v:string)
               (e:nnrc)
               (i:nat)
               (eol:estring)
               (quotel:estring)
               (ivs : list string)
               (fname:string)
      := let e' := closeFreeVars jsSafeSeparator jsIdentifierSanitize (NNRCVar input_v) e ivs in
         nnrcToJSFunStubConstantsAsMethod e' i eol quotel ivs fname.

    (* Java equivalent: JavaScriptBackend.generateJavaScript *)
    Definition nnrc_to_js_top (e:nnrc) : ejavascript :=
      let input_f := "query" in
      let input_v := "constants" in
      let init_indent := 0 in
      nnrcToJSFun input_v e init_indent eol_newline quotel_double (input_v::nil) input_f.

    Definition nnrc_to_js_top_with_name (e:nnrc) (fname:string) : ejavascript :=
      let input_v := "constants" in
      let init_indent := 0 in
      nnrcToJSFun input_v e init_indent eol_newline quotel_double (input_v::nil) fname.

  End NNRCJS.

  Section CodeGenTest.
    
    Definition e_in : nnrc :=
      NNRCBinop OpRecConcat
                (NNRCUnop (UnaryOperators.OpRec "a")
                          (NNRCLet "p1"
                                   (NNRCConst (dstring "hi"))
                                   (NNRCVar "p1")))
                (NNRCUnop (OpRec "b")
                          (NNRCLet "p1"
                                   (NNRCConst (dstring "boo"))
                                   (NNRCVar "p1"))).

    Definition test_gen (e:nnrc) :=
      nnrc_to_js_top e_in.

    Definition test_gen_rename (e:nnrc) : ejavascript :=
      nnrc_to_js_top (rename_top e_in).

(*    
    Eval vm_compute in rename_top e_in.
    Eval vm_compute in test_gen e_in.
    Eval vm_compute in test_gen_rename e_in.
 *)

  End CodeGenTest.
End ENNRCtoJavaScript.
