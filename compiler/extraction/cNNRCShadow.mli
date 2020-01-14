open Bag
open CoqLibAdd
open Datatypes
open EquivDec
open ForeignRuntime
open List0
open String0
open UnaryOperators
open Var
open CNNRC
open CNNRCVars

val pick_new_really_fresh_in :
  foreign_runtime -> char list -> var -> var list -> nnrc -> char list

val pick_same_really_fresh_in :
  foreign_runtime -> char list -> var -> var list -> nnrc -> char list

val nnrc_rename_lazy : foreign_runtime -> nnrc -> var -> var -> nnrc

val nnrc_pick_name :
  foreign_runtime -> char list -> (char list -> char list) -> var list -> var
  -> nnrc -> char list

val unshadow :
  foreign_runtime -> char list -> (char list -> char list) -> var list ->
  nnrc -> nnrc

val nnrc_subst_const_to_var :
  foreign_runtime -> char list list -> nnrc -> nnrc

val closeFreeVars :
  foreign_runtime -> char list -> (char list -> char list) -> nnrc -> nnrc ->
  char list list -> nnrc
