open List0

type nstring = string

val nstring_quote : char list -> nstring

val nstring_append : nstring -> nstring -> nstring

val nstring_flat_map : (char -> nstring) -> nstring -> nstring

val nstring_concat : nstring -> nstring list -> nstring

val nstring_map_concat : nstring -> ('a1 -> nstring) -> 'a1 list -> nstring
