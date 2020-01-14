open CoqLibAdd
open Datatypes
open EquivDec
open ForeignRuntime
open Fresh
open List0
open Var
open CNNRC

val nnrc_global_vars : foreign_runtime -> nnrc -> var list

val nnrc_bound_vars : foreign_runtime -> nnrc -> var list

val nnrc_free_vars : foreign_runtime -> nnrc -> var list

val nnrc_subst : foreign_runtime -> nnrc -> var -> nnrc -> nnrc

val really_fresh_in :
  foreign_runtime -> char list -> var -> var list -> nnrc -> char list
