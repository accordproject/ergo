open CoqLibAdd
open EquivDec

type 'foreign_ejson_model foreign_ejson = { foreign_ejson_dec : 'foreign_ejson_model
                                                                coq_EqDec;
                                            foreign_ejson_normalize : 
                                            ('foreign_ejson_model ->
                                            'foreign_ejson_model);
                                            foreign_ejson_tostring : 
                                            'foreign_ejson_model coq_ToString }
