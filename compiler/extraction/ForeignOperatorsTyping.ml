open ForeignOperators
open RType

type foreign_operators_typing = { foreign_operators_typing_unary_infer : 
                                  (foreign_operators_unary -> rtype -> rtype
                                  option);
                                  foreign_operators_typing_unary_infer_sub : 
                                  (foreign_operators_unary -> rtype ->
                                  (rtype * rtype) option);
                                  foreign_operators_typing_binary_infer : 
                                  (foreign_operators_binary -> rtype -> rtype
                                  -> rtype option);
                                  foreign_operators_typing_binary_infer_sub : 
                                  (foreign_operators_binary -> rtype -> rtype
                                  -> ((rtype * rtype) * rtype) option) }
