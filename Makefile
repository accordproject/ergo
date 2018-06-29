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

FILES = $(addprefix mechanization/,$(MODULES:%=%.v))

## Compiler
all:
	@$(MAKE) MAKEFLAGS= ergo

# Regenerate the npm directory
ergo: _CoqProject Makefile.coq
	@$(MAKE) ergo-mechanization
	@$(MAKE) MAKEFLAGS= ergo-extraction-refresh

ergo-mechanization: _CoqProject Makefile.coq
	@echo "[Ergo] "
	@echo "[Ergo] Compiling Coq Mechanization"
	@echo "[Ergo] "
	@$(MAKE) -f Makefile.coq

ergo-extraction:
	@echo "[Ergo] "
	@echo "[Ergo] Compiling the extracted OCaml"
	@echo "[Ergo] "
	@$(MAKE) -C extraction all

ergo-extraction-refresh:
	@echo "[Ergo] "
	@echo "[Ergo] Extracting mechanization to OCaml"
	@echo "[Ergo] "
	@$(MAKE) -C extraction all-refresh

ergo-npm:
	lerna bootstrap

publish:
	lerna bootstrap && lerna publish --force-publish=*

## Documentation
documentation:
	$(MAKE) -C mechanization documentation
	./scripts/build_api_md.sh

## Testing
test:
	lerna run test

## Cleanup
clean-mechanization: Makefile.coq
	- @$(MAKE) -f Makefile.coq clean

cleanall-mechanization:
	- @$(MAKE) -f Makefile.coq cleanall
	- @rm -f Makefile.coq
	- @rm -f Makefile.coq.conf
	- @rm -f _CoqProject

clean-extraction:
	- @$(MAKE) -C extraction clean

cleanall-extraction:
	- @$(MAKE) -C extraction cleanall

clean-npm:
	- @rm -f package-lock.json
	- @rm -rf dist

cleanall-npm: clean-npm
	- @rm -f ergo*.tgz
	- @rm -rf node_modules
	- @rm -rf .nyc_output
	- @rm -rf coverage
	- @rm -rf log
	- @rm -f lerna-debug.log

clean: Makefile.coq
	- @$(MAKE) clean-npm
	- @$(MAKE) clean-extraction
	- @$(MAKE) -C packages/ergo-compiler clean
	- @$(MAKE) -C packages/ergo-engine clean
	- @$(MAKE) -C packages/ergo-cli clean

cleanall: Makefile.coq
	- @$(MAKE) cleanall-npm
	- @$(MAKE) cleanall-extraction
	- @$(MAKE) cleanall-mechanization
	- @$(MAKE) cleanall-npm
	- @$(MAKE) -C packages/ergo-compiler cleanall
	- @$(MAKE) -C packages/ergo-engine cleanall
	- @$(MAKE) -C packages/ergo-cli cleanall

##
_CoqProject: Makefile.config
ifneq ($(QCERT),)
	(echo "-R mechanization ErgoSpec -R $(QCERT)/coq Qcert";) > _CoqProject
else
	(echo "-R mechanization ErgoSpec";) > _CoqProject
endif

Makefile.coq: _CoqProject Makefile $(FILES)
	coq_makefile -f _CoqProject $(FILES) -o Makefile.coq

.PHONY: all clean documentation npm ergo

