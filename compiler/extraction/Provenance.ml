open CoqLibAdd
open String0
open ToString

type location_point = { offset : int; line : int; column : int }

type location = { loc_file : char list; loc_start : location_point;
                  loc_end : location_point }

(** val dummy_location : location **)

let dummy_location =
  let dummy_location_point = { offset = ((~-) 1); line = ((~-) 1); column =
    ((~-) 1) }
  in
  { loc_file = []; loc_start = dummy_location_point; loc_end =
  dummy_location_point }

type provenance =
| ProvFunc of location * char list
| ProvClause of location * char list
| ProvThisContract of location
| ProvThisClause of location
| ProvThisState of location
| ProvLoc of location

(** val dummy_provenance : provenance **)

let dummy_provenance =
  ProvLoc dummy_location

(** val loc_of_provenance : provenance -> location **)

let loc_of_provenance = function
| ProvFunc (loc, _) -> loc
| ProvClause (loc, _) -> loc
| ProvThisContract loc -> loc
| ProvThisClause loc -> loc
| ProvThisState loc -> loc
| ProvLoc loc -> loc

(** val string_of_location_point : location_point -> char list **)

let string_of_location_point lp =
  append (toString coq_ToString_Z lp.line)
    (append (':'::[]) (toString coq_ToString_Z lp.column))

(** val string_of_location_no_file : location -> char list **)

let string_of_location_no_file loc =
  let file = [] in
  append file
    (append (string_of_location_point loc.loc_start)
      (append ('-'::[]) (string_of_location_point loc.loc_end)))
