open ForeignData
open ForeignEJsonRuntime

type ('foreign_ejson_model, 'foreign_ejson_runtime_op) foreign_to_ejson = { 
foreign_to_ejson_runtime : ('foreign_ejson_runtime_op, 'foreign_ejson_model)
                           foreign_ejson_runtime;
foreign_to_ejson_to_data : ('foreign_ejson_model -> foreign_data_model);
foreign_to_ejson_from_data : (foreign_data_model -> 'foreign_ejson_model) }
