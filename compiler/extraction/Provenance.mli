open CoqLibAdd
open String0
open ToString

type location_point = { offset : int; line : int; column : int }

type location = { loc_file : char list; loc_start : location_point;
                  loc_end : location_point }

val dummy_location : location

type provenance =
| ProvFunc of location * char list
| ProvClause of location * char list
| ProvThisContract of location
| ProvThisClause of location
| ProvThisState of location
| ProvLoc of location

val dummy_provenance : provenance

val loc_of_provenance : provenance -> location

val string_of_location_point : location_point -> char list

val string_of_location_no_file : location -> char list
