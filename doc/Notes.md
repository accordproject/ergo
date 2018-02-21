Compilation for switch expressions:

```
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

with `v0` fresh in `[[e1]]`, `[[e2]]` and `[[edefault]]` `_v1` fresh
in `[[e2]]` and `[[edefault]]` and `_v2` fresh in `[[edefault]]`.

