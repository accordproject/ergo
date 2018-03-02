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
JURA_HOME=$(CURDIR)/..

############# Shouldn't have to be changed after this
OCAMLBUILD= ocamlbuild \
		-no-links -classic-display \
		-tags annot -use-ocamlfind -package atdgen -package unix -package base64

MENHIRFLAG=-use-menhir
#MENHIRFLAG=

## Mains
MAIN=jurac
MAIN2=juracore

TARGET=native

## Toplevel
all: ../bin/$(MAIN).$(TARGET) ../packages/jura-compiler/lib/$(MAIN2).js

all-refresh: extracted/JComp.ml extracted/JComp.mli ../bin/$(MAIN).$(TARGET) ../packages/jura-compiler/lib/$(MAIN2).js

js: ../packages/jura-compiler/lib/$(MAIN2).js

## Extraction
VO_FILES = $(MODULES:%=../mechanization/%.vo)

extracted/StaticConfig.ml:
	mkdir -p extracted
	echo "(* This file is generated *)" > extracted/StaticConfig.ml
	echo "let qcert_home = \"$(QCERT_HOME)\"" >> extracted/StaticConfig.ml
	echo "let jura_home = \"$(JURA_HOME)\"" >> extracted/StaticConfig.ml

extracted/JComp.ml extracted/JComp.mli: $(VO_FILES)
	mkdir -p extracted
ifneq ($(QCERT),)
	(cd extracted; coqc -R ../../mechanization Jura -R ../../$(QCERT)/coq Qcert ../JuraExtraction.v)
else
	(cd extracted; coqc -R ../../mechanization Jura ../JuraExtraction.v)
endif

## ATDs

src/Cto_t.ml src/Cto_t.mli: src/Cto.atd
	atdgen -t $<

src/Cto_j.ml src/Cto_j.mli: src/Cto.atd
	atdgen -j -j-std $<

ATDS=src/Cto_t.ml src/Cto_t.mli src/Cto_j.ml src/Cto_j.mli

## Native
../bin/$(MAIN).$(TARGET): $(ATDS) extracted/StaticConfig.ml extracted/JComp.ml extracted/JComp.mli $(MAIN).$(TARGET)
	cp _build/$(MAIN).$(TARGET) ../bin/$(MAIN).$(TARGET)

$(MAIN).$(TARGET): $(ATDS) extracted/StaticConfig.ml extracted/JComp.ml extracted/JComp.mli
	$(OCAMLBUILD) $(MENHIRFLAG) -Is extracted -Is src $(MAIN).$(TARGET)

## JavaScript
../packages/jura-compiler/lib/$(MAIN2).js: $(ATDS) extracted/StaticConfig.ml extracted/JComp.ml extracted/JComp.mli _build_js/$(MAIN2).byte
	js_of_ocaml _build_js/$(MAIN2).byte
	cp _build_js/$(MAIN2).js ../packages/jura-compiler/lib/$(MAIN2).js

_build_js/$(MAIN2).byte: $(ATDS) $(MAIN).$(TARGET) extracted/StaticConfig.ml extracted/JComp.ml extracted/JComp.mli $(MAIN2).ml
	$(OCAMLBUILD) $(MENHIRFLAG) -build-dir _build_js -use-ocamlfind -package js_of_ocaml -package js_of_ocaml.ppx -Is extracted -Is src $(MAIN2).byte

## Clean

clean:
	ocamlbuild -clean -no-log
	rm -rf _build
	rm -rf _build_js
	rm -f ../bin/$(MAIN).$(TARGET)
	rm -f extracted/StaticConfig.ml
	rm -f $(ATDS)

cleanall: clean
	rm -f JuraExtraction.glob JuraExtraction.vo .JuraExtraction.aux
	rm -rf *~
	rm -f extracted/JComp.ml extracted/JComp.mli

.NOTPARALLEL: 

