(*
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

Section ENames.
  Require Import String.
  Local Open Scope string.

  Section ScopedNames.
    Definition namespace_ref := option string.

    Record class_ref :=
      mkClassRef
        { class_namespace : namespace_ref;
          class_name : string; }.

  End ScopedNames.

  Section AbsoluteNames.
    Definition absolute_ref := string.

    Definition absolute_ref_of_class_ref (local_namespace:option string) (cr:class_ref) :=
      match cr.(class_namespace) with
      | None =>
        match local_namespace with
        | None => cr.(class_name)
        | Some namespace => namespace ++ "." ++ cr.(class_name)
        end
      | Some ref_package => ref_package ++ "." ++ cr.(class_name)
      end.
  End AbsoluteNames.    
    
End ENames.
