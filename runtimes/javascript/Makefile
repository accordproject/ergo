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

############# Shouldn't have to be changed after this
all: ergo-runtime.js ergo_runtime.ml

ergo-runtime.js: ergo-runtime-core.js ergo-runtime-tostring.js ergo-runtime-date-time.js ergo-runtime-uri.js ergo-runtime-math.js ergo-runtime-log.js
	(for i in ergo-runtime-core.js ergo-runtime-tostring.js ergo-runtime-date-time.js ergo-runtime-uri.js ergo-runtime-math.js ergo-runtime-log.js; do \
         cat $$i; \
         done) > ergo-runtime.js

ergo_runtime.ml: ergo-runtime.js
	(echo "let runtime = {runtime|"; \
         cat ergo-runtime.js; \
         echo '|runtime}' \
         ) > ergo_runtime.ml

clean:
	-rm -f ergo-runtime.js ergo_runtime.ml
	-rm -f *~

cleanall: clean

