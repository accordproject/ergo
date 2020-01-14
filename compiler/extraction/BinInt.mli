open BinNat
open BinPos
open Datatypes

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val opp : int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val compare : int -> int -> comparison

  val sgn : int -> int

  val max : int -> int -> int

  val min : int -> int -> int

  val abs : int -> int

  val to_nat : int -> int

  val of_nat : int -> int

  val of_N : int -> int

  val quotrem : int -> int -> int * int

  val quot : int -> int -> int

  val rem : int -> int -> int

  val log2 : int -> int

  val sqrt : int -> int

  val eq_dec : int -> int -> bool
 end
