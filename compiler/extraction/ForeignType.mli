open EquivDec
open Lattice

type __ = Obj.t

type foreign_type = { foreign_type_dec : __ coq_EqDec;
                      foreign_type_lattice : __ coq_Lattice;
                      foreign_type_sub_dec : (__ -> __ -> bool) }

type foreign_type_type = __
