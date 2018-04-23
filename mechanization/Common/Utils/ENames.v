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

Require Import String.

Section ENames.
  Local Open Scope string.

  Section ScopedNames.
    Definition relative_ref := string.
    Definition namespace_ref := option string.

    Record class_ref :=
      mkClassRef
        { class_namespace : namespace_ref;
          class_name : relative_ref; }.

  End ScopedNames.

  Section AbsoluteNames.
    Definition absolute_ref := string.

    Definition absolute_ref_of_relative_ref (namespace: string) (rr: relative_ref) : absolute_ref :=
      namespace ++ "." ++ rr.

    Definition absolute_ref_of_class_ref (local_namespace:string) (cr:class_ref) : absolute_ref :=
      let namespace :=
          match cr.(class_namespace) with
          | None => local_namespace
          | Some namespace_ref => namespace_ref
          end
      in
      absolute_ref_of_relative_ref namespace cr.(class_name).
      
  End AbsoluteNames.    
    
End ENames.
