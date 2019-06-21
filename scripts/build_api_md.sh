#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# 
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

npm install -g jsdoc-to-markdown

## Build the Ergo API
jsdoc2md -c ./scripts/ergo-jsdoc.conf --files ./packages/**/*.js > ./docs/ergo-api-js.md
jsdoc2md --template ./scripts/ergo-api-js.hbs -c ./scripts/ergo-jsdoc.conf --files ./packages/**/*.js > ./docs/ergo-api-js.md
