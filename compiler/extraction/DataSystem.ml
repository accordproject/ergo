open ForeignRuntime
open ForeignType
open ForeignTyping
open TBrandModel

type basic_model = { basic_model_runtime : foreign_runtime;
                     basic_model_foreign_type : foreign_type;
                     basic_model_brand_model : brand_model;
                     basic_model_foreign_typing : foreign_typing }
