open ForeignData
open ForeignOperators
open Java
open NativeString

type foreign_to_java = { foreign_to_java_data : (nstring ->
                                                foreign_data_model ->
                                                java_json);
                         foreign_to_java_unary_op : (int -> nstring ->
                                                    nstring ->
                                                    foreign_operators_unary
                                                    -> java_json ->
                                                    java_json);
                         foreign_to_java_binary_op : (int -> nstring ->
                                                     nstring ->
                                                     foreign_operators_binary
                                                     -> java_json ->
                                                     java_json -> java_json) }
