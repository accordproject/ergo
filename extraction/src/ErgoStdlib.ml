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

open Resources

let ergo_stdcto =
  [ ("$ERGODIR/extraction/stdlib/accordproject.cto", accordproject);
    ("$ERGODIR/extraction/stdlib/contract.cto", contract);
    ("$ERGODIR/extraction/stdlib/money.cto", money);
    ("$ERGODIR/extraction/stdlib/time.cto", time);
    ("$ERGODIR/extraction/stdlib/options.cto", options);
    ("$ERGODIR/extraction/stdlib/runtime.cto", runtime);
    ("$ERGODIR/extraction/stdlib/commonmark.cto", commonmark);
    ("$ERGODIR/extraction/stdlib/ciceromark.cto", ciceromark); ]
let ergo_stdlib =
  [ ("$ERGODIR/extraction/stdlib/stdlib.ergo", stdlib);
    ("$ERGODIR/extraction/stdlib/etime.ergo", etime);
    ("$ERGODIR/extraction/stdlib/template.ergo", template) ];

