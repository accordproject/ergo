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

let monitor = {xxx|
{"type":"Program","namespace":"org.accordproject.ergo.monitor","imports":[],"body":[{"type":"ConceptDeclaration","id":{"type":"Identifier","name":"Phase"},"classExtension":null,"body":{"type":"ClassDeclarationBody","declarations":[{"type":"FieldDeclaration","id":{"type":"Identifier","name":"name"},"propertyType":{"name":"String"},"array":null,"regex":null,"default":null,"optional":null,"decorators":[],"location":{"start":{"offset":735,"line":21,"column":3},"end":{"offset":751,"line":22,"column":3}}},{"type":"FieldDeclaration","id":{"type":"Identifier","name":"single"},"propertyType":{"name":"Double"},"array":null,"range":null,"default":null,"optional":null,"decorators":[],"location":{"start":{"offset":751,"line":22,"column":3},"end":{"offset":769,"line":23,"column":3}}},{"type":"FieldDeclaration","id":{"type":"Identifier","name":"cummulative"},"propertyType":{"name":"Double"},"array":null,"range":null,"default":null,"optional":null,"decorators":[],"location":{"start":{"offset":769,"line":23,"column":3},"end":{"offset":792,"line":24,"column":3}}},{"type":"FieldDeclaration","id":{"type":"Identifier","name":"total"},"propertyType":{"name":"Double"},"array":null,"range":null,"default":null,"optional":null,"decorators":[],"location":{"start":{"offset":792,"line":24,"column":3},"end":{"offset":809,"line":25,"column":3}}},{"type":"FieldDeclaration","id":{"type":"Identifier","name":"subphases"},"propertyType":{"type":"Identifier","name":"Phase"},"array":"[]","default":null,"optional":null,"decorators":[],"location":{"start":{"offset":809,"line":25,"column":3},"end":{"offset":829,"line":26,"column":1}}}],"location":{"start":{"offset":735,"line":21,"column":3},"end":{"offset":829,"line":26,"column":1}}},"abstract":null,"decorators":[],"location":{"start":{"offset":717,"line":20,"column":1},"end":{"offset":830,"line":26,"column":2}}},{"type":"ConceptDeclaration","id":{"type":"Identifier","name":"Monitor"},"classExtension":null,"body":{"type":"ClassDeclarationBody","declarations":[{"type":"FieldDeclaration","id":{"type":"Identifier","name":"phases"},"propertyType":{"type":"Identifier","name":"Phase"},"array":"[]","default":null,"optional":null,"decorators":[],"location":{"start":{"offset":871,"line":32,"column":3},"end":{"offset":888,"line":33,"column":1}}}],"location":{"start":{"offset":871,"line":32,"column":3},"end":{"offset":888,"line":33,"column":1}}},"abstract":null,"decorators":[],"location":{"start":{"offset":851,"line":31,"column":1},"end":{"offset":889,"line":33,"column":2}}}]}
|xxx}
