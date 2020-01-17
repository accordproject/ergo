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

# User-level configuration
include Makefile.config
# Contains the list of all the Coq modules
include Makefile.coq_modules

#
CP=cp

FILES = $(addprefix compiler/core/,$(MODULES:%=%.v))

## Compiler
all:
	@$(MAKE) prepare
	@$(MAKE) MAKEFLAGS= ergo

# Stdlib

%.ctoj: %.cto
	./scripts/cto2ctoj.js parse $<

compiler/lib/resources.ml: compiler/stdlib/accordproject.ctoj \
                           compiler/stdlib/stdlib.ergo \
                           compiler/stdlib/etime.ergo \
                           compiler/stdlib/template.ergo \
                           runtimes/javascript/ergo-runtime.js
	echo '(* generated ocaml file *)' > compiler/lib/resources.ml
	(for i in accordproject; do \
         echo "let $$i = {xxx|"; \
         cat compiler/stdlib/$$i.ctoj; \
         echo "|xxx}"; \
         done) >> compiler/lib/resources.ml
	(for i in stdlib etime template; do \
         echo "let $$i = {xxx|"; \
         cat compiler/stdlib/$$i.ergo; \
         echo "|xxx}"; \
         done) >> compiler/lib/resources.ml
	(for i in runtime; do \
         echo "let ergo_$$i = {xxx|"; \
         cat ./runtimes/javascript/ergo-$$i.js; \
         echo "|xxx}"; \
         done) >> compiler/lib/resources.ml
	(echo `date "+let builddate = {xxx|%b %d, %Y|xxx}"`) >> compiler/lib/resources.ml

# Configure
runtimes/javascript/ergo-runtime.js: runtimes/javascript/ergo-runtime-core.js \
                           runtimes/javascript/ergo-runtime-date-time.js \
                           runtimes/javascript/ergo-runtime-log.js \
                           runtimes/javascript/ergo-runtime-math.js \
                           runtimes/javascript/ergo-runtime-uri.js
	$(MAKE) -C ./runtimes/javascript

./compiler/lib/js_runtime.ml: ./runtimes/javascript/ergo_runtime.ml
	cp ./runtimes/javascript/ergo_runtime.ml ./compiler/lib/js_runtime.ml

./compiler/lib/static_config.ml:
	echo "(* This file is generated *)" > ./compiler/lib/static_config.ml
	echo "let ergo_home = \"$(CURDIR)\"" >> ./compiler/lib/static_config.ml

prepare: ./compiler/lib/static_config.ml compiler/lib/resources.ml Makefile.coq
	$(MAKE) -C ./runtimes/javascript

configure:
	@echo "[Ergo] "
	@echo "[Ergo] Configuring Build"
	@echo "[Ergo] "
	npm install
	@$(MAKE) prepare

# Regenerate the npm directory
ergo:
	@$(MAKE) ergo-mechanization
	@$(MAKE) MAKEFLAGS= ergo-ocaml-extraction
	@$(MAKE) MAKEFLAGS= ergo-js-extraction

ergo-mechanization: _CoqProject Makefile.coq
	@echo "[Ergo] "
	@echo "[Ergo] Compiling Coq Mechanization"
	@echo "[Ergo] "
	@$(MAKE) -f Makefile.coq

ergo-ocaml-extraction:
	@echo "[Ergo] "
	@echo "[Ergo] Extracting Ergo Compiler to OCaml"
	@echo "[Ergo] "
	@$(MAKE) -C compiler/extraction
	dune build @install

ergo-js-extraction:
	@echo "[Ergo] "
	@echo "[Ergo] Extracting Ergo Compiler to JavaScript"
	@echo "[Ergo] "
	@$(MAKE) -C compiler/libjs

## Documentation
documentation:
	$(MAKE) -C compiler/core documentation

## Testing
test:
	lerna run test

## Cleanup
clean-mechanization: Makefile.coq
	- @$(MAKE) -f Makefile.coq clean

cleanall-mechanization:
	- @$(MAKE) -f Makefile.coq cleanall
	- @rm -f ./compiler/lib/js_runtime.ml ./compiler/lib/static_config.ml compiler/lib/resources.ml
	- @rm -f Makefile.coq
	- @rm -f Makefile.coq.conf
	- @rm -f _CoqProject
	- @find compiler/core \( -name '*.vo' -or -name '*.v.d' -or -name '*.glob'  -or -name '*.aux' \) -print0 | xargs -0 rm -f

clean-ocaml-extraction:
	- @$(MAKE) -C compiler/extraction clean

cleanall-ocaml-extraction:
	- @$(MAKE) -C compiler/extraction cleanall
	- dune clean

clean-js-extraction:
	- @$(MAKE) -C compiler/libjs clean

cleanall-js-extraction:
	- @$(MAKE) -C compiler/libjs cleanall

clean-npm:

cleanall-npm: clean-npm
	- @node ./scripts/external/cleanExternalModels.js
	- @rm -f ergo*.tgz
	- @rm -rf node_modules
	- @rm -rf .nyc_output
	- @rm -rf coverage
	- @rm -rf log
	- @rm -f lerna-debug.log

clean: Makefile.coq
	- @$(MAKE) clean-npm
	- @$(MAKE) clean-ocaml-extraction
	- @$(MAKE) clean-js-extraction
	- @$(MAKE) -C packages/ergo-compiler clean
	- @$(MAKE) -C packages/ergo-engine clean
	- @$(MAKE) -C packages/ergo-cli clean
	- @$(MAKE) -C runtimes/javascript clean

cleanall: Makefile.coq
	@echo "[Ergo] "
	@echo "[Ergo] Cleaning up"
	@echo "[Ergo] "
	- @$(MAKE) cleanall-npm
	- @$(MAKE) cleanall-ocaml-extraction
	- @$(MAKE) cleanall-mechanization
	- @$(MAKE) -C packages/ergo-compiler cleanall
	- @$(MAKE) -C packages/ergo-engine cleanall
	- @$(MAKE) -C packages/ergo-cli cleanall
	- @$(MAKE) -C runtimes/javascript cleanall

##
_CoqProject: Makefile.config
	@echo "[Ergo] "
	@echo "[Ergo] Setting up Coq"
	@echo "[Ergo] "
ifneq ($(QCERT),)
	(echo "-R compiler/core ErgoSpec -R $(QCERT)/compiler/core Qcert";) > _CoqProject
else
	(echo "-R compiler/core ErgoSpec";) > _CoqProject
endif

Makefile.coq: _CoqProject Makefile $(FILES)
	coq_makefile -f _CoqProject $(FILES) -o Makefile.coq

.PHONY: all clean documentation npm ergo

