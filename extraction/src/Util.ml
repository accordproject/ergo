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

(* This module contains a few basic utilities *)

(* Ergo Exception *)

exception Ergo_Error of string

(* this can't go in Logger, since that creates a circular dependency *)
type nra_logger_token_type = string
type nrc_logger_token_type = string
type dnrc_logger_token_type = string

(**************)
(* Data types *)
(**************)

(* Data type conversions between Coq and OCaml *)

let rec string_of_char_list l =
  begin match l with
  | [] -> ""
  | c :: l -> (String.make 1 c) ^ (string_of_char_list l)
  end

let char_list_of_string s =
  let l = ref [] in
  String.iter (fun c -> l := c :: !l) s;
  List.rev !l

let string = string_of_char_list

(* coq Z's are now replaced by native OCaml ints, but here is the way to get things back to coq Z's:

   open BinNums

   let rec coq_nat_of_pos i =
   if i = 0 then Datatypes.O else Datatypes.S (coq_nat_of_pos (i-1))

   let coq_positive_of_pos i =
   BinPos.Pos.of_nat (coq_nat_of_pos i)

   let coq_Z_of_int i =
   if (i = 0) then Z0
   else if (i < 0)
   then (Zneg (coq_positive_of_pos (-i)))
   else (Zpos (coq_positive_of_pos i))
*)

let coq_Z_of_int i = i


(*******)
(* I/O *)
(*******)

(* Temporarily disabled -- JS
   let os_newline = if Sys.win32 then "\r\n" else "\n" *)
let os_newline = "\n"

let string_of_file file =
  try
    let inchan = open_in_bin file in
    let len = in_channel_length inchan in
    let buf = Buffer.create len in
    Buffer.add_channel buf inchan len;
    close_in inchan;
    Buffer.contents buf
  with
    Sys_error err ->
      Printf.eprintf
        "Could not read the file %s, got error Sys_error %s\n@?"
        file
        err;
      raise(Sys_error err)

(* File print *)

let make_file fout scomp =
  let oc = open_out fout in
  begin
    output_string oc scomp;
    close_out oc
  end

(* Make up target file name *)

let target_f dir f =
  begin match dir with
  | None -> f
  | Some d ->
      Filename.concat d (Filename.basename f)
  end

let outname f suff = f ^ suff


(**********)
(* Lookup *)
(**********)

let get_data x io =
  try List.assoc x io
  with Not_found ->
    Printf.fprintf stderr "Unbound variable %s\n" x;
    raise (Ergo_Error ("Unbound variable" ^ x))

let get_data_raise x io =
  List.assoc x io


(**********************************)
(* Support for Enhanced operators *)
(**********************************)

let float_sum l =
  List.fold_left (+.) 0. l

(* note that this is inefficient, becase it uses two passes over the list *)
let float_arithmean l =
  let ll = List.length l in
  if(ll == 0)
  then 0.
  else List.fold_left (+.) 0. l /. (float ll)

let rec float_listmin_aux l x =
  begin match l with
  | [] -> x
  | c :: ls -> float_listmin_aux ls (if x<c then x else c)
  end

let float_listmin l =
  begin match l with
  | [] -> infinity
  | c :: ls -> float_listmin_aux ls c
  end

let rec float_listmax_aux l x =
  begin match l with
  | [] -> x
  | c :: ls -> float_listmax_aux ls (if x>c then x else c)
  end

let float_listmax l =
  begin match l with
  | [] -> neg_infinity
  | c :: ls -> float_listmax_aux ls c
  end

let qcert_string_of_float f =
  let ocaml_string = string_of_float f in
  let last_char = ocaml_string.[(String.length ocaml_string)-1] in
  begin match last_char with
  | '.' -> ocaml_string ^ "0"
  | _ -> ocaml_string
  end

let string_of_enhanced_float f = char_list_of_string (string_of_float f)
let string_of_enhanced_string s = char_list_of_string ("S\"" ^ s ^ "\"")

(**********************************)
(* Timing function for CompStat   *)
(**********************************)

let time f x =
  let start = Sys.time() in
  let v = f x in
  let stop = Sys.time() in
  let t = string_of_float (stop -. start) in
  (char_list_of_string t, v)

(* String manipulation *)    

let string_before s n = String.sub s 0 n
let string_after s n = String.sub s n (String.length s - n)
let first_chars s n = String.sub s 0 n
let last_chars s n = String.sub s (String.length s - n) n

let re_match re s pos =
  if pos >= String.length s then raise Not_found
  else
    let rec pos_match re s pos_re pos_s =
      if pos_re >= String.length re
      then true
      else
        try
          if re.[pos_re] = s.[pos_s]
          then pos_match re s (pos_re+1) (pos_s+1)
          else false
        with
        | _ -> false
    in
    pos_match re s 0 pos

let search_forward re s pos =
  if re = "" then raise (Invalid_argument "Matching string should not be empty")
  else
    let rec find start =
      if re_match re s start
      then start
      else find (start+1)
    in
    find pos

let opt_search_forward re s pos =
  try Some(search_forward re s pos) with Not_found -> None

let global_replace const_expr repl text =
  let rec replace accu start last_was_empty =
    let startpos = if last_was_empty then start + 1 else start in
    if startpos > String.length text then
      string_after text start :: accu
    else
      begin match opt_search_forward const_expr text startpos with
      | None ->
          string_after text start :: accu
      | Some pos ->
          let end_pos = pos + String.length const_expr in
          let repl_text = repl in
          replace (repl_text :: String.sub text start (pos-start) :: accu)
            end_pos (end_pos = pos)
      end
  in
  String.concat "" (List.rev (replace [] 0 false))

(** Additional utility functions *)

let process_file f file_name =
  Format.printf "Processing file: %s --" file_name;
  let file_content = string_of_file file_name in
  try f (file_name,file_content) with
  | Ergo_Error msg ->
      raise (Ergo_Error ("In file [" ^ file_name ^ "] " ^ msg))

