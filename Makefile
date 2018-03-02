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
	@$(MAKE) MAKEFLAGS= jura

# Regenerate the npm directory
jura: _CoqProject Makefile.coq
	@$(MAKE) jura-mechanization
	@$(MAKE) MAKEFLAGS= jura-extraction-refresh
	@$(MAKE) jura-npm

jura-mechanization: _CoqProject Makefile.coq
	@echo "[Jura] "
	@echo "[Jura] Compiling Coq Mechanization"
	@echo "[Jura] "
	@$(MAKE) -f Makefile.coq

jura-extraction:
	@echo "[Jura] "
	@echo "[Jura] Compiling the extracted OCaml"
	@echo "[Jura] "
	@$(MAKE) -C extraction all

jura-extraction-refresh:
	@echo "[Jura] "
	@echo "[Jura] Extracting mechanization to OCaml"
	@echo "[Jura] "
	@$(MAKE) -C extraction all-refresh

jura-npm:
	npm install

npm-package:
	npm install && npm pack


## Documentation
documentation:
	@$(MAKE) -C mechanization documentation

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
	- @rm -f jura*.tgz
	- @rm -rf node_modules
	- @rm -rf .nyc_output
	- @rm -rf coverage
	- @rm -rf log

clean: Makefile.coq
	- @$(MAKE) clean-npm
	- @$(MAKE) clean-extraction
	- @$(MAKE) clean-mechanization
	- @$(MAKE) -C packages/jura-compiler clean
	- @$(MAKE) -C packages/jura-cli clean
	- @rm -f *~

cleanall: Makefile.coq
	- @$(MAKE) cleanall-npm
	- @$(MAKE) cleanall-extraction
	- @$(MAKE) cleanall-mechanization
	- @$(MAKE) cleanall-npm
	- @$(MAKE) -C packages/jura-compiler cleanall
	- @$(MAKE) -C packages/jura-cli cleanall
	- @rm -f *~

##
_CoqProject: Makefile.config
ifneq ($(QCERT),)
	(echo "-R mechanization Jura -R $(QCERT)/coq Qcert";) > _CoqProject
else
	(echo "-R mechanization Jura";) > _CoqProject
endif

Makefile.coq: _CoqProject Makefile $(FILES)
	coq_makefile -f _CoqProject $(FILES) -o Makefile.coq

.PHONY: all clean documentation npm jura

