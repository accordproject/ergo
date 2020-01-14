
type ejson_op =
| EJsonOpNot
| EJsonOpNeg
| EJsonOpAnd
| EJsonOpOr
| EJsonOpLt
| EJsonOpLe
| EJsonOpGt
| EJsonOpGe
| EJsonOpAddString
| EJsonOpAddNumber
| EJsonOpSub
| EJsonOpMult
| EJsonOpDiv
| EJsonOpStrictEqual
| EJsonOpStrictDisequal
| EJsonOpArray
| EJsonOpArrayLength
| EJsonOpArrayPush
| EJsonOpArrayAccess
| EJsonOpObject of char list list
| EJsonOpAccess of char list
| EJsonOpHasOwnProperty of char list
| EJsonOpMathMin
| EJsonOpMathMax
| EJsonOpMathPow
| EJsonOpMathExp
| EJsonOpMathAbs
| EJsonOpMathLog
| EJsonOpMathLog10
| EJsonOpMathSqrt
| EJsonOpMathCeil
| EJsonOpMathFloor
| EJsonOpMathTrunc
