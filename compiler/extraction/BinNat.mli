open BinPos
open Datatypes

module N :
 sig
  val succ_double : int -> int

  val double : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val pos_div_eucl : int -> int -> int * int

  val to_nat : int -> int

  val of_nat : int -> int
 end
