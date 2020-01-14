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

(* This module contains the implementation for the optimization logger *)

open SExp

type logger_verbosity =
  | LOG_NONE
  | LOG_NAMES
  | LOG_PHASES_AND_NAMES
  | LOG_VERBOSE_SEXP of (Obj.t -> sexp)

let logger_verbosity_of_string conv s
  = match s with
  | "none" -> LOG_NONE
  | "names" -> LOG_NAMES
  | "phases_and_names" -> LOG_PHASES_AND_NAMES
  | "sexp" -> LOG_VERBOSE_SEXP conv
  | _ -> raise (Failure ("Unknown logging verbosity level: "^s^".  Supported levels: none, names, phases_and_names, sexp"))

(* TODO: refactor this code *)
	    
(* nrc logger *)
  
let nrc_trace = ref LOG_NONE
let nrc_set_trace conv s = nrc_trace := (logger_verbosity_of_string conv s)

let nrc_log_startPass name input =
  if !nrc_trace != LOG_NONE
  then
    (begin
	match !nrc_trace with
	| LOG_PHASES_AND_NAMES ->
	   print_string "starting nrc optimization pass: "; print_endline name
	| LOG_VERBOSE_SEXP conv -> print_string ("(phase \"nrc\" \""^name^"\"")
	| _ -> ()
    end;
     name)
  else
    name
  
let nrc_log_step tok name input output =
  if !nrc_trace != LOG_NONE
  then
    begin
     if (input == output)
      then () (* (print_string "skipping optimization: "; print_endline name) *)
      else
	begin
	  match !nrc_trace with
	  | LOG_NAMES ->
	     (print_string "running nrc optimization: "; print_endline name) ;
	  | LOG_PHASES_AND_NAMES ->
	     (print_string "  running nrc optimization: "; print_endline name) ;
	  | LOG_VERBOSE_SEXP conv ->
	     begin
	       let sexp_input = conv (Obj.magic input) in
	       let sexp_output = conv (Obj.magic output) in
	       let sexp_opt = STerm ("opt", [SString name; sexp_input; sexp_output]) in
	       print_endline ""; print_string ("  " ^ (sexp_to_string sexp_opt))
	     end
	  | _ -> ()
	end;
     tok
    end
  else
    tok

let nrc_log_endPass tok output =
  if !nrc_trace != LOG_NONE
  then
    (begin
	match !nrc_trace with
	| LOG_PHASES_AND_NAMES ->
	   print_endline "ending nrc optimization pass: "
	| LOG_VERBOSE_SEXP conv -> print_endline ")"
	| _ -> ()
    end;
     tok)
  else
    tok

let log_string x =
  Printf.printf "%s\n" (Util.string_of_char_list x)

