# Notes

Compilation for switch expressions:

```text
[[ switch e0 {
     case let v1 as type1: e1
     case let v2 as type2: e2
     default: edefault
   } ]]
==
let v0 := [[ e0 ]] in
  match cast v0 as type1
  | left as v1 -> [[ e1 ]]
  | right as _v1 ->
    match cast v0 as type2
    | left as v2 -> [[ e2 ]]
    | right as _v2 -> [[ edefault ]]
```

with `v0` fresh in `[[e1]]`, `[[e2]]` and `[[edefault]]` `_v1` fresh in `[[e2]]` and `[[edefault]]` and `_v2` fresh in `[[edefault]]`.

Dispatching:

A set of clauses:

```text
c0(P0 ;; P01, P02)
c1(P1 ;; P11, P12)
c2(P2 ;; P22, P22)
```

where one allows dispatch on the first argument, is treated as a switch on the type of their first parameters:

```text
define dispatch(p0, p1, p2) {
  switch p0 {
    case v0 as P0:
      c0(v0, p1, p2)
    case v1 as P1:
      c1(v1, p1, p2)
    case v2 as P2:
      c2(v2, p1, p2)
    default:
      new Error{ "Dispatch failed" }
  }
}
```

