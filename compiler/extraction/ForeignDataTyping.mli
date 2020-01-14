open ForeignData
open ForeignType

type __ = Obj.t

type foreign_data_typing = { foreign_data_typing_infer : (foreign_data_model
                                                         -> foreign_type_type
                                                         option);
                             foreign_data_typing_infer_normalized : (foreign_data_model
                                                                    -> __ ->
                                                                    foreign_type_type) }
