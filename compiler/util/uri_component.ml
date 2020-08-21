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

let encode x =
  Util.char_list_of_string (Uri.pct_encode ~component:`Scheme (Util.string_of_char_list x))
let decode x =
  Util.char_list_of_string (Uri.pct_decode (Util.string_of_char_list x))

