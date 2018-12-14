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

(* This module contains pretty-printers for intermediate languages *)

open Format

open PrettyCommon
open ErgoComp

(** Pretty query wrapper *)

type 'a pretty_fun = bool -> int -> bool -> json -> bool -> 'a -> string
	
(** Pretty NNRC *)

let rec pretty_nnrc_aux p sym ff n =
  match n with
  | NNRCGetConstant v -> fprintf ff "$$%s"  (Util.string_of_char_list v)
  | NNRCVar v -> fprintf ff "$v%s"  (Util.string_of_char_list v)
  | NNRCConst d -> fprintf ff "%a" pretty_data d
  | NNRCBinop (b,n1,n2) -> (pretty_binary_op p sym pretty_nnrc_aux) ff b n1 n2
  | NNRCUnop (u,n1) -> (pretty_unary_op p sym pretty_nnrc_aux) ff u n1
  | NNRCLet (v,n1,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>let $v%s :=@ %a@]@;<1 0>@[<hv 2>in@ %a@]@]"
	 (Util.string_of_char_list v)
	(pretty_nnrc_aux p sym) n1
	(pretty_nnrc_aux p sym) n2
  | NNRCFor (v,n1,n2) ->
      fprintf ff "@[<hv 0>{ @[<hv 0>%a@]@;<1 0>@[<hv 2>| $v%s %a@ %a@] }@]"
	(pretty_nnrc_aux 0 sym) n2
	 (Util.string_of_char_list v) pretty_sym sym.sin
	(pretty_nnrc_aux 0 sym) n1
  | NNRCIf (n1,n2,n3) ->
      fprintf ff "@[<hv 0>@[<hv 2>if@;<1 0>%a@]@;<1 0>@[<hv 2>then@;<1 0>%a@]@;<1 0>@[<hv 2>else@;<1 0>%a@]@]"
	(pretty_nnrc_aux p sym) n1
	(pretty_nnrc_aux p sym) n2
	(pretty_nnrc_aux p sym) n3
  | NNRCEither (n0,v1,n1,v2,n2) ->
      fprintf ff "@[<hv 0>@[<hv 2>match@ %a@;<1 -2>with@]@;<1 0>@[<hv 2>| left as $v%s ->@ %a@]@;<1 0>@[<hv 2>| right as $v%s ->@ %a@]@;<1 -2>@[<hv 2>end@]@]"
	(pretty_nnrc_aux p sym) n0
	 (Util.string_of_char_list v1) (pretty_nnrc_aux p sym) n1
	(Util.string_of_char_list v2) (pretty_nnrc_aux p sym) n2
  | NNRCGroupBy (g,atts,n1) ->
      fprintf ff "@[<hv 2>group by@ %a%a@[<hv 2>(%a)@]@]" (pretty_squared_names sym) [g] (pretty_squared_names sym) atts (pretty_nnrc_aux 0 sym) n1

let pretty_nnrc greek margin annot inheritance link_runtime q =
  let ff = str_formatter in
  let sym = if greek then greeksym else textsym in
  begin
    pp_set_margin ff margin;
    fprintf ff "@[%a@]@." (pretty_nnrc_aux 0 sym) q;
    flush_str_formatter ()
  end

let pretty_nnrc_declaration p sym ff dl =
  begin match dl with
  | DNExpr e -> fprintf ff "EXPR:@.%a" (pretty_nnrc_aux p sym) e
  | DNConstant (s,e) -> fprintf ff "CONSTANT:@.%a" (pretty_nnrc_aux p sym) e
  | DNFunc f -> fprintf ff "FUNCTION: %s@.%a" (Util.string_of_char_list f.functionn_name) (pretty_nnrc_aux p sym) (f.functionn_lambda.lambdan_body)
  | DNFuncTable ft -> ()
  end
let rec pretty_nnrc_declarations p sym ff dls =
  begin match dls with
  | [] -> ()
  | dl :: [] ->
      fprintf ff "%a"
        (pretty_nnrc_declaration p sym) dl
  | dl :: dls' ->
      fprintf ff "%a@.%a"
        (pretty_nnrc_declaration p sym) dl
        (pretty_nnrc_declarations p sym) dls'
  end

let pretty_nnrc_module greek margin annot inheritance link_runtimesym q =
  let ff = str_formatter in
  let sym = if greek then greeksym else textsym in
  begin
    pp_set_margin ff margin;
    fprintf ff "@[%a@]@." (pretty_nnrc_declarations 0 sym) q.modulen_declarations;
    flush_str_formatter ()
  end

(** Pretty Error *)

let pretty_error greek margin annot inheritance link_runtime q =
  "Error: "^(Util.string_of_char_list q)

