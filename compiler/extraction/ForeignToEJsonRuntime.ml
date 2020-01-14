open ForeignOperators

type ('foreign_ejson_model, 'foreign_ejson_runtime_op) foreign_to_ejson_runtime = { 
foreign_to_ejson_runtime_of_unary_op : (foreign_operators_unary ->
                                       'foreign_ejson_runtime_op);
foreign_to_ejson_runtime_of_binary_op : (foreign_operators_binary ->
                                        'foreign_ejson_runtime_op) }
