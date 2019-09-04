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
open Monitor_j (* For the monitor JSON output *)

(* this can't go in Logger, since that creates a circular dependency *)
type nrc_logger_token_type = string

(** Conversions *)
let string_of_char_list l =
  let b = Bytes.create (List.length l) in
  let i = ref 0 in
  List.iter (fun c -> Bytes.set b !i c; incr i) l;
  Bytes.to_string b

let char_list_of_string s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let char_list_append s1 s2 =
  char_list_of_string ((string_of_char_list s1) ^ (string_of_char_list s2))

let coq_Z_of_int i = i


(** I/O *)
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
      raise (Sys_error err)

(** File print *)
let make_file fout scomp =
  let oc = open_out fout in
  begin
    output_string oc scomp;
    close_out oc
  end

(** Make up target file name *)
let target_f dir f =
  begin match dir with
  | None -> f
  | Some d ->
      Filename.concat d (Filename.basename f)
  end

let outname f suff = f ^ suff

(** Support for Enhanced operators *)

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
  begin match classify_float f with
  | FP_normal | FP_subnormal | FP_zero ->
      let ocaml_string1 = Printf.sprintf "%.17g" f in (* XXX TO BE REVIEWED *)
      let ocaml_string2 = Printf.sprintf "%.16g" f in (* XXX TO BE REVIEWED *)
      let ocaml_string =
        if (float_of_string ocaml_string1 = float_of_string ocaml_string2)
        then ocaml_string2 else ocaml_string1
      in
      let ocaml_string =
        match String.index_opt ocaml_string '.', String.index_opt ocaml_string 'e' with
        | None, None -> ocaml_string ^ "."
        | _, _ -> ocaml_string
      in
      let last_char = ocaml_string.[(String.length ocaml_string)-1] in
      begin match last_char with
      | '.' -> ocaml_string ^ "0"
      | _ -> ocaml_string
      end
  | FP_nan -> "NaN"
  | _ ->
      string_of_float f
  end

let string_of_enhanced_float f = char_list_of_string (qcert_string_of_float f)
let string_of_enhanced_string s = char_list_of_string ("S\"" ^ s ^ "\"")
let ergo_float_of_string s =
  begin try
    Some (float_of_string (string_of_char_list s))
  with _ -> None
  end

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

let filename_append dir path =
  List.fold_left Filename.concat dir path

let loc_error s f x =
  begin try f x with
  | Failure exn -> raise (Failure exn)
  | exn -> raise (Failure ("[In " ^ s ^ "]" ^ (Printexc.to_string exn)))
  end

let map_assoc f l =
   List.map (fun xy -> f (fst xy) (snd xy)) l

(** Mini topo-sort *)
(* XXX To be revised when Coq-level DFS-topological sort is complete *)

exception TopoCycle of string list

let dfs label name graph visited start_node = 
  let rec explore path visited node = 
    if List.mem (label node) (List.map label path) then raise (TopoCycle (List.map name (node::path))) else
    if List.mem (label node) (List.map label visited) then visited else     
      let new_path = node :: path in 
      let edges    = List.assoc (label node) (List.map (fun (x,y) -> (label x, y)) graph) in
      let visited  = List.fold_left (explore new_path) visited edges in
      node :: visited
  in explore [] visited start_node

let toposort label name graph = 
  List.rev (List.fold_left (fun visited (node,_) -> dfs label name graph visited node) [] graph)

let print_order msg name o =
  if (false)
  then
    begin
      Printf.printf "\n=====\n%s\n=====\n" msg;
      List.iter (fun x -> Printf.printf "ITEM: %s\n" (name x)) o;
      flush stdout
    end

let compare_of_order o labely labelx name x1 x2 =
  if labelx x1 = labelx x2 then 0
  else
    let fl = List.filter (fun x -> labely x = labelx x1 || labely x = labelx x2) o in
    begin match fl with
    | [] | _ :: [] ->
        raise (Failure ("Could not find request types ["
                        ^ (string_of_char_list (labelx x1))
                        ^ ", "
                        ^ (string_of_char_list (labelx x2))
                        ^  "] during dispatch creation"))
    | y1 :: y2 :: [] ->
        if labelx x1 = labely y1
        then +1
        else -1
    | y1 :: y2 :: y3 :: _ ->
        if (labely y1 = labely y2)
        then raise (Failure ("Duplicates for " ^ (name y1)))
        else raise (Failure ("Duplicates for " ^ (name y2)))
    end

let coq_distinct name l =
  print_order "DISTINCT" (fun x -> string_of_char_list (name x)) l;
  let l = List.sort_uniq compare l in
  print_order "DISTINCT OUPUT" (fun x -> string_of_char_list (name x)) l;
  l

let sort_given_topo_order order labely labelx name l =
  print_order "SORT GIVEN TOPO" name order;
  let comp = compare_of_order order labely labelx name in
  List.sort comp l

let coq_toposort label name graph =
  let sorted = toposort label (fun x -> string_of_char_list (name x)) graph in
  sorted

let coq_sort_given_topo_order order labely labelx name l =
  let sorted = sort_given_topo_order order labely labelx (fun x -> string_of_char_list (name x)) l in
  sorted

(* Tests

let g = [("request1",["top"]);
         ("request6",["request4"]);
         ("request3",["request1"]);
         ("top",[]);
         ("request4",["request1"]);
         ("request2",["request1"]);
         ("request5",["top"])];;

let label x = x;;
let print x = x;;
let test1 = toposort label label g;;

let test2 =
  assert (sort_with_topo_order label label print g
  ["request6";"request1";"request3";"request4"]
  = ["request3"; "request6"; "request4"; "request1"]);;

let test3 =
  assert (sort_given_topo_order label label print test1
  ["request6";"request1";"request3";"request4"]
  = ["request3"; "request6"; "request4"; "request1"]);;

let test4 =
  assert (sort_given_topo_order label label print test1
  ["request6";"request1";"request3";"top";"request4"]
  = ["request3"; "request6"; "request4"; "request1"; "top"]);;
*)

let get_local_part name =
  let name = string_of_char_list name in
  begin match String.rindex_opt name '.' with
  | None -> None
  | Some i ->
      let local = String.sub name (i+1) (String.length name - (i+1)) in
      Some (char_list_of_string local)
  end

let class_prefix_of_filename filename =
  begin try
    Filename.chop_extension (Filename.basename filename)
  with
  | Invalid_argument _ -> "logic"
  end

(** Monitoring *)

(* monitor contains a mapping from compilation phase to (f1,f2) where f1 is the new time entering the phase and f2 is the total time in that phase *)
let monitor : (string, float * float) Hashtbl.t = Hashtbl.create 37
let monitoring = ref false
let monitoring_start = Sys.time ()
let monitor_output : (Monitor_j.phase list) Stack.t =
  let s = Stack.create () in
  Stack.push [] s;
  s

let enter_monitor monitor output phase =
  Stack.push [] output;
  begin try
    let (f1,f2) = Hashtbl.find monitor phase in (* f1 should always be 0.0 *)
    Hashtbl.replace monitor phase (Sys.time(), f2)
  with _ ->
    Hashtbl.add monitor phase (Sys.time(), 0.0)
  end
let exit_monitor monitor output phase =
  let prev = Stack.pop output in
  let prevprev = Stack.pop output in
  begin try
    let (f1,f2) = Hashtbl.find monitor phase in
    let picktime : float = Sys.time () in
    let single : float = picktime -. f1 in
    let cummul : float = picktime -. f1 +. f2 in
    let total : float = picktime -. monitoring_start in
    Hashtbl.replace monitor phase (0.0, cummul);
    Stack.push (prevprev @ [{
      monitor_phase_class = "org.accordproject.ergo.monitor.Phase";
      monitor_phase_name = phase;
      monitor_phase_single = single;
      monitor_phase_cummulative = cummul;
      monitor_phase_total = total;
      monitor_phase_subphases =prev
    }]) output
  with _ ->
    begin
      let picktime : float = Sys.time () in
      let single : float = 0.0 in
      let cummul : float = 0.0 in
      let total : float = picktime -. monitoring_start in
      Hashtbl.add monitor phase (0.0, 0.0); (* Should never happen *)
      Stack.push (prevprev @ [{
        monitor_phase_class = "org.accordproject.ergo.monitor.Phase";
        monitor_phase_name = phase;
        monitor_phase_single = single;
        monitor_phase_cummulative = cummul;
        monitor_phase_total = total;
        monitor_phase_subphases = prev
      }]) output
    end
  end

let coq_time phase f x =
  if !monitoring
  then
    let phase = string_of_char_list phase in
    begin
      enter_monitor monitor monitor_output phase;
      let y = f x in
      exit_monitor monitor monitor_output phase;
      y
    end
  else
    f x

let get_monitor_output () =
  string_of_monitor {
    monitor_class = "org.accordproject.ergo.monitor.Monitor";
    monitor_phases = Stack.top monitor_output
  }

let flat_map_string f s =
  let sl = ref [] in
  String.iter (fun c -> sl := (f c) :: !sl) s;
  let sl' = List.rev !sl in
  String.concat "" sl'

exception Dup of char list
let comp_for_fun s1 s2 =
  let c = compare s1 s2 in
  if c = 0
  then raise (Dup s1)
  else c

let find_duplicate sl =
  begin try
    ignore(List.sort comp_for_fun sl);
    None
  with
  | Dup s ->
      Some s
  end

let coq_print_warning prefix warning =
  Printf.printf "[WARNING][%s] %s\n" prefix (string_of_char_list warning)

let coq_print_warnings prefix warnings x =
  List.iter (coq_print_warning (string_of_char_list prefix)) warnings;
  x

open Uri
let encode_string x =
  char_list_of_string (Uri.pct_encode ~component:`Query (string_of_char_list x))
let decode_string x =
  char_list_of_string (Uri.pct_decode (string_of_char_list x))

