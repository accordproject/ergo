open CoqLibAdd
open EquivDec

type __ = Obj.t

type foreign_data = { foreign_data_dec : __ coq_EqDec;
                      foreign_data_normalize : (__ -> __);
                      foreign_data_tostring : __ coq_ToString }

type foreign_data_model = __
