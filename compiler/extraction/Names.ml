open String0

type local_name = char list

type namespace_name = char list

type enum_name = char list

type namespace_prefix = namespace_name option

type relative_name = namespace_prefix * local_name

type absolute_name = char list

(** val absolute_name_of_local_name :
    namespace_name -> local_name -> absolute_name **)

let absolute_name_of_local_name ns ln =
  append ns (append ('.'::[]) ln)

(** val enum_namespace : namespace_name -> enum_name -> namespace_name **)

let enum_namespace ns en =
  append ns (append ('.'::[]) en)

(** val clause_main_name : local_name **)

let clause_main_name =
  'm'::('a'::('i'::('n'::[])))

(** val clause_init_name : local_name **)

let clause_init_name =
  'i'::('n'::('i'::('t'::[])))

(** val this_this : char list **)

let this_this =
  '_'::('_'::('t'::('h'::('i'::('s'::[])))))

(** val this_contract : char list **)

let this_contract =
  '_'::('_'::('c'::('o'::('n'::('t'::('r'::('a'::('c'::('t'::[])))))))))

(** val this_state : char list **)

let this_state =
  '_'::('_'::('s'::('t'::('a'::('t'::('e'::[]))))))

(** val this_emit : char list **)

let this_emit =
  '_'::('_'::('e'::('m'::('i'::('t'::[])))))

(** val this_response : char list **)

let this_response =
  '_'::('_'::('r'::('e'::('s'::('p'::('o'::('n'::('s'::('e'::[])))))))))

(** val local_state : char list **)

let local_state =
  '_'::('_'::('l'::('s'::('t'::('a'::('t'::('e'::[])))))))

(** val local_emit : char list **)

let local_emit =
  '_'::('_'::('l'::('e'::('m'::('i'::('t'::[]))))))

(** val current_time : char list **)

let current_time =
  '_'::('_'::('n'::('o'::('w'::[]))))

(** val options : char list **)

let options =
  '_'::('_'::('o'::('p'::('t'::('i'::('o'::('n'::('s'::[]))))))))

(** val accordproject_concerto_namespace : char list **)

let accordproject_concerto_namespace =
  'c'::('o'::('n'::('c'::('e'::('r'::('t'::('o'::[])))))))

(** val accordproject_runtime_namespace : char list **)

let accordproject_runtime_namespace =
  'o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('r'::('u'::('n'::('t'::('i'::('m'::('e'::[]))))))))))))))))))))))))

(** val accordproject_contract_namespace : char list **)

let accordproject_contract_namespace =
  'o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('c'::('o'::('n'::('t'::('r'::('a'::('c'::('t'::[])))))))))))))))))))))))))

(** val accordproject_stdlib_namespace : char list **)

let accordproject_stdlib_namespace =
  'o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('s'::('t'::('d'::('l'::('i'::('b'::[]))))))))))))))))))))))))))))

(** val accordproject_time_namespace : char list **)

let accordproject_time_namespace =
  'o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('t'::('i'::('m'::('e'::[])))))))))))))))))))))

(** val accordproject_top_namespace : char list **)

let accordproject_top_namespace =
  'o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('t'::('o'::('p'::[])))))))))))))))))))))))))

(** val accordproject_options_namespace : char list **)

let accordproject_options_namespace =
  'o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('o'::('p'::('t'::('i'::('o'::('n'::('s'::[])))))))))))))))))))))))))))))

(** val accordproject_template_namespace : char list **)

let accordproject_template_namespace =
  'o'::('r'::('g'::('.'::('a'::('c'::('c'::('o'::('r'::('d'::('p'::('r'::('o'::('j'::('e'::('c'::('t'::('.'::('e'::('r'::('g'::('o'::('.'::('t'::('e'::('m'::('p'::('l'::('a'::('t'::('e'::[]))))))))))))))))))))))))))))))

(** val default_enum_absolute_name : char list **)

let default_enum_absolute_name =
  absolute_name_of_local_name accordproject_concerto_namespace
    ('E'::('n'::('u'::('m'::[]))))

(** val default_event_absolute_name : char list **)

let default_event_absolute_name =
  absolute_name_of_local_name accordproject_concerto_namespace
    ('E'::('v'::('e'::('n'::('t'::[])))))

(** val default_transaction_absolute_name : char list **)

let default_transaction_absolute_name =
  absolute_name_of_local_name accordproject_concerto_namespace
    ('T'::('r'::('a'::('n'::('s'::('a'::('c'::('t'::('i'::('o'::('n'::[])))))))))))

(** val default_asset_absolute_name : char list **)

let default_asset_absolute_name =
  absolute_name_of_local_name accordproject_concerto_namespace
    ('A'::('s'::('s'::('e'::('t'::[])))))

(** val default_participant_absolute_name : char list **)

let default_participant_absolute_name =
  absolute_name_of_local_name accordproject_concerto_namespace
    ('P'::('a'::('r'::('t'::('i'::('c'::('i'::('p'::('a'::('n'::('t'::[])))))))))))

(** val default_contract_absolute_name : char list **)

let default_contract_absolute_name =
  absolute_name_of_local_name accordproject_contract_namespace
    ('C'::('o'::('n'::('t'::('r'::('a'::('c'::('t'::[]))))))))

(** val default_clause_absolute_name : char list **)

let default_clause_absolute_name =
  absolute_name_of_local_name accordproject_contract_namespace
    ('C'::('l'::('a'::('u'::('s'::('e'::[]))))))

(** val default_request_absolute_name : char list **)

let default_request_absolute_name =
  absolute_name_of_local_name accordproject_runtime_namespace
    ('R'::('e'::('q'::('u'::('e'::('s'::('t'::[])))))))

(** val default_state_absolute_name : char list **)

let default_state_absolute_name =
  absolute_name_of_local_name accordproject_runtime_namespace
    ('S'::('t'::('a'::('t'::('e'::[])))))

(** val default_error_absolute_name : char list **)

let default_error_absolute_name =
  absolute_name_of_local_name accordproject_stdlib_namespace
    ('E'::('r'::('r'::('o'::('r'::[])))))

(** val default_options : char list **)

let default_options =
  absolute_name_of_local_name accordproject_options_namespace
    ('O'::('p'::('t'::('i'::('o'::('n'::('s'::[])))))))

(** val function_name_in_table :
    char list option -> char list -> char list **)

let function_name_in_table tname fname =
  match tname with
  | Some tname0 -> append tname0 (append ('_'::[]) fname)
  | None -> fname

(** val no_namespace : char list **)

let no_namespace =
  []
