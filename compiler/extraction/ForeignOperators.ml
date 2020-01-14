open BrandRelation
open CoqLibAdd
open Data
open EquivDec

type __ = Obj.t

type foreign_operators = { foreign_operators_unary_dec : __ coq_EqDec;
                           foreign_operators_unary_tostring : __ coq_ToString;
                           foreign_operators_unary_interp : (brand_relation_t
                                                            -> __ -> data ->
                                                            data option);
                           foreign_operators_binary_dec : __ coq_EqDec;
                           foreign_operators_binary_tostring : __
                                                               coq_ToString;
                           foreign_operators_binary_interp : (brand_relation_t
                                                             -> __ -> data ->
                                                             data -> data
                                                             option);
                           foreign_operators_unary_data_tostring : (data ->
                                                                   char list);
                           foreign_operators_unary_data_totext : (data ->
                                                                 char list) }

type foreign_operators_unary = __

type foreign_operators_binary = __
