open CoqLibAdd
open EJson
open EquivDec

type ('foreign_ejson_runtime_op, 'foreign_ejson_model) foreign_ejson_runtime = { 
foreign_ejson_runtime_op_dec : 'foreign_ejson_runtime_op coq_EqDec;
foreign_ejson_runtime_op_tostring : 'foreign_ejson_runtime_op coq_ToString;
foreign_ejson_runtime_op_interp : ('foreign_ejson_runtime_op ->
                                  'foreign_ejson_model ejson list ->
                                  'foreign_ejson_model ejson option);
foreign_ejson_runtime_tostring : ('foreign_ejson_model ejson -> char list);
foreign_ejson_runtime_fromstring : (char list -> 'foreign_ejson_runtime_op
                                   option);
foreign_ejson_runtime_totext : ('foreign_ejson_model ejson -> char list) }
