if exists("b:current_syntax")
  finish
endif


syn keyword ergoKeyword define set
syn keyword ergoKeyword contract clause over


syn region ergoNamespace start="namespace" end="\n"
syn region ergoNamespace start="import" end="\n"

syn keyword ergoStatement enforce emit call
syn match ergoStatement "set state"
syn keyword ergoStatement foreach in where return match with then if else let throw

syn keyword ergoSpecialName some none nil now state

syn match ergoOperator "+"
syn match ergoOperator "-"
syn match ergoOperator "*"
syn match ergoOperator "/"
syn match ergoOperator "\^"

syn match ergoOperator ">"
syn match ergoOperator ">="
syn match ergoOperator "<"
syn match ergoOperator "<="

syn match ergoOperator "?"
syn match ergoOperator "??"


syn match ergoOperator "="
syn match ergoOperator "!="

syn match ergoOperator " and "
syn match ergoOperator " or "
syn match ergoOperator "!"

syn match ergoOperator "\~"
syn match ergoOperator "++"

syn match ergoOperator ":"
syn match ergoOperator ","
syn match ergoOperator ";"

syn match ergoComment "//.*"
syn region ergoComment matchgroup=ergoComment start="/\*" end="\*/" contains=ergoComment

syn region ergoString start="\"" skip="\\\"" end="\"" contains=elmStringEscape
syn match ergoStringEscape "\\u[0-9a-fA-F]\{4}" contained
syn match ergoStringEscape "\\[nrfvbt\\\"]" contained

syn match ergoNumber "\(\<\d\+\>\)"
syn match ergoNumber "\(\<\d\+\.\d\+\>\)"

syn keyword ergoBoolean true
syn keyword ergoBoolean false

syn keyword ergoPrimType constant function abstract concept transaction participant event asset enum extends
syn keyword ergoPrimType Integer Long Double String DateTime
syn match ergoPrimType " [A-Z][A-Za-z]*"

let b:current_syntax = "ergo"

hi def link ergoKeyword Keyword
hi def link ergoNamespace PreProc
hi def link ergoStatement Statement
hi def link ergoSpecialName Constant
hi def link ergoOperator Operator
hi def link ergoPrimType Type
hi def link ergoComment Comment
hi def link ergoString String
hi def link ergoNumber Number
hi def link ergoBoolean Boolean
