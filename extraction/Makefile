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
include ../Makefile.config
# Contains the list of all the Coq modules
include ../Makefile.coq_modules

## Configuraton
QCERT_HOME=$(QCERT)
ERGO_HOME=$(CURDIR)/..

############# Shouldn't have to be changed after this
OCAMLBUILD= ocamlbuild \
		-no-links -classic-display \
		-tags annot -use-ocamlfind -package atdgen -package unix -package base64 -package re.str -package calendar

MENHIRFLAG=-use-menhir
#MENHIRFLAG=

## Mains
NATIVE=native
BYTE=byte
JS=js
ML=ml

TARGET0=ergotop.$(NATIVE)
MAIN0=ergotop
BYTE0=$(MAIN0).$(BYTE)
BIN0=$(MAIN0).$(NATIVE)
DIST0=../bin/$(TARGET0)

TARGET1=ergoc.$(NATIVE)
MAIN1=ergocML
BYTE1=$(MAIN1).$(BYTE)
BIN1=$(MAIN1).$(NATIVE)
DIST1=../bin/$(TARGET1)

TARGET2=ergo-core.$(JS)
MAIN2=ergocoreJS
BYTE2=$(MAIN2).$(BYTE)
BIN2=$(MAIN2).$(JS)
DIST2=../packages/ergo-compiler/lib/$(TARGET2)

TARGET3=ergoc-lib.$(JS)
MAIN3=ergocJS
BYTE3=$(MAIN3).$(BYTE)
BIN3=$(MAIN3).$(JS)
DIST3=../packages/ergo-cli/lib/$(TARGET3)

TARGET4=ergodep.$(NATIVE)
MAIN4=ergodep
BYTE4=$(MAIN4).$(BYTE)
BIN4=$(MAIN4).$(NATIVE)
DIST4=../bin/$(TARGET4)

TARGET5=ergotop-lib.$(JS)
MAIN5=ergotopJS
BYTE5=$(MAIN5).$(BYTE)
BIN5=$(MAIN5).$(JS)
DIST5=../packages/ergo-cli/lib/$(TARGET5)

## Toplevel
all: $(DIST0) $(DIST1) $(DIST2) $(DIST3) $(DIST4) $(DIST5)

all-refresh: extracted/ErgoComp.ml extracted/ErgoComp.mli $(DIST0) $(DIST1) $(DIST2) $(DIST3) $(DIST4) $(DIST5)

top: $(DIST0)

js: $(DIST2) $(DIST3) $(DIST4) $(DIST5)

## Extraction
VO_FILES = $(MODULES:%=../mechanization/%.vo)

extracted/ErgoComp.ml extracted/ErgoComp.mli: $(VO_FILES)
	mkdir -p extracted
ifneq ($(QCERT),)
	(cd extracted; coqc -R ../../mechanization ErgoSpec -R ../../$(QCERT)/coq Qcert ../ErgoExtraction.v)
else
	(cd extracted; coqc -R ../../mechanization ErgoSpec ../ErgoExtraction.v)
endif

## ATDs
src/Cto_t.ml src/Cto_t.mli: src/Cto.atd
	atdgen -t $<

src/Cto_j.ml src/Cto_j.mli: src/Cto.atd
	atdgen -j -j-std $<

ATDS=src/Cto_t.ml src/Cto_t.mli src/Cto_j.ml src/Cto_j.mli

## Stdlib

%.ctoj: %.cto
	../scripts/cto2ctoj.js parse $<

extracted/StdlibResources.ml: stdlib/contract.ctoj stdlib/hyperledger.ctoj stdlib/money.ctoj stdlib/runtime.ctoj stdlib/dom.ctoj stdlib/stdlib.ergo
	echo '(* generated ocaml file *)' > extracted/StdlibResources.ml
	(for i in contract hyperledger money runtime; do \
         echo "let $$i = {xxx|"; \
         cat stdlib/$$i.ctoj; \
         echo '|xxx}'; \
         done) >> extracted/StdlibResources.ml
	(for i in stdlib; do \
         echo "let $$i = {xxx|"; \
         cat stdlib/$$i.ergo; \
         echo '|xxx}'; \
         done) >> extracted/StdlibResources.ml

## Native
$(DIST0): $(ATDS) extracted/StdlibResources.ml extracted/ErgoComp.ml extracted/ErgoComp.mli $(BIN0)
	cp _build/$(BIN0) $(DIST0)

$(BIN0): $(ATDS) extracted/StdlibResources.ml extracted/ErgoComp.ml extracted/ErgoComp.mli $(MAIN0).$(ML)
	$(OCAMLBUILD) $(MENHIRFLAG) -Is extracted -Is src $(BIN0)

$(DIST1): $(ATDS) extracted/StdlibResources.ml extracted/ErgoComp.ml extracted/ErgoComp.mli $(BIN1)
	cp _build/$(BIN1) $(DIST1)

$(BIN1): $(ATDS) extracted/StdlibResources.ml extracted/ErgoComp.ml extracted/ErgoComp.mli $(MAIN1).$(ML)
	$(OCAMLBUILD) $(MENHIRFLAG) -Is extracted -Is src $(BIN1)

$(DIST4): $(ATDS) extracted/StdlibResources.ml extracted/ErgoComp.ml extracted/ErgoComp.mli $(BIN4)
	cp _build/$(BIN4) $(DIST4)

$(BIN4): $(ATDS) extracted/StdlibResources.ml extracted/ErgoComp.ml extracted/ErgoComp.mli $(MAIN4).$(ML)
	$(OCAMLBUILD) $(MENHIRFLAG) -Is extracted -Is src $(BIN4)

## JavaScript
$(DIST2): $(ATDS) extracted/StdlibResources.ml extracted/ErgoComp.ml extracted/ErgoComp.mli _build_js/$(BYTE2) $(DIST1)
	js_of_ocaml _build_js/$(BYTE2) -o _build_js/$(BIN2)
	cp _build_js/$(BIN2) $(DIST2)

_build_js/$(BYTE2): $(ATDS) extracted/StdlibResources.ml extracted/ErgoComp.ml extracted/ErgoComp.mli $(MAIN2).$(ML)
	$(OCAMLBUILD) $(MENHIRFLAG) -build-dir _build_js -use-ocamlfind -package js_of_ocaml -package js_of_ocaml.ppx -Is extracted -Is src $(BYTE2)

$(DIST3): $(ATDS) extracted/StdlibResources.ml extracted/ErgoComp.ml extracted/ErgoComp.mli _build_js/$(BYTE3) $(DIST1)
	js_of_ocaml _build_js/$(BYTE3) -o _build_js/$(BIN3)
	cp _build_js/$(BIN3) $(DIST3)

_build_js/$(BYTE3): $(ATDS) extracted/StdlibResources.ml extracted/ErgoComp.ml extracted/ErgoComp.mli $(MAIN3).$(ML)
	$(OCAMLBUILD) $(MENHIRFLAG) -build-dir _build_js -use-ocamlfind -package js_of_ocaml -package js_of_ocaml.ppx -Is extracted -Is src $(BYTE3)

$(DIST5): $(ATDS) extracted/StdlibResources.ml extracted/ErgoComp.ml extracted/ErgoComp.mli _build_js/$(BYTE5) $(DIST1)
	js_of_ocaml _build_js/$(BYTE5) -o _build_js/$(BIN5)
	cp _build_js/$(BIN5) $(DIST5)

_build_js/$(BYTE5): $(ATDS) extracted/StdlibResources.ml extracted/ErgoComp.ml extracted/ErgoComp.mli $(MAIN5).$(ML)
	$(OCAMLBUILD) $(MENHIRFLAG) -build-dir _build_js -use-ocamlfind -package js_of_ocaml -package js_of_ocaml.ppx -Is extracted -Is src $(BYTE5)

## Clean

clean:
	ocamlbuild -clean -no-log
	rm -rf _build
	rm -rf _build_js
	rm -f $(DIST0)
	rm -f $(DIST1)
	rm -f extracted/StdlibResources.ml
	rm -f stdlib/*.ctoj
	rm -f $(ATDS)

cleanall: clean
	rm -f ErgoExtraction.glob ErgoExtraction.vo .ErgoExtraction.aux
	rm -rf *~
	rm -f extracted/ErgoComp.ml extracted/ErgoComp.mli

.NOTPARALLEL: 

