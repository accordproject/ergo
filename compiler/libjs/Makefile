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
include ../../Makefile.config
# Contains the list of all the Coq modules
include ../../Makefile.coq_modules

## Configuraton
ERGO_HOME=$(CURDIR)/../..

BYTECODE=bc
JS=js

## Mains
MAIN1=compilerJS
TARGET1=$(ERGO_HOME)/packages/ergo-compiler/extracted/compilercore.$(JS)
MAIN2=ergocJS
TARGET2=$(ERGO_HOME)/packages/ergo-cli/extracted/ergoccore.$(JS)
MAIN3=ergotopJS
TARGET3=$(ERGO_HOME)/packages/ergo-cli/extracted/ergotopcore.$(JS)

## Toplevel
all:
	dune build $(MAIN1).$(BYTECODE) $(MAIN2).$(BYTECODE) $(MAIN3).$(BYTECODE)
	$(MAKE) $(TARGET1) $(TARGET2) $(TARGET3)

## JavaScript
$(TARGET1): $(ERGO_HOME)/_build/default/compiler/libjs/$(MAIN1).$(BYTECODE)
	js_of_ocaml $(ERGO_HOME)/_build/default/compiler/libjs/$(MAIN1).$(BYTECODE)
	cp $(ERGO_HOME)/_build/default/compiler/libjs/$(MAIN1).$(JS) $(TARGET1)

$(TARGET2): $(ERGO_HOME)/_build/default/compiler/libjs/$(MAIN2).$(BYTECODE)
	dune build $(MAIN2).$(BYTECODE)
	js_of_ocaml $(ERGO_HOME)/_build/default/compiler/libjs/$(MAIN2).$(BYTECODE)
	cp $(ERGO_HOME)/_build/default/compiler/libjs/$(MAIN2).$(JS) $(TARGET2)

$(TARGET3): $(ERGO_HOME)/_build/default/compiler/libjs/$(MAIN3).$(BYTECODE)
	js_of_ocaml $(ERGO_HOME)/_build/default/compiler/libjs/$(MAIN3).$(BYTECODE)
	cp $(ERGO_HOME)/_build/default/compiler/libjs/$(MAIN3).$(JS) $(TARGET3)

## Clean

clean:

cleanall: clean
	rm -f $(TARGET1).$(JS)
	rm -f $(TARGET2).$(JS)
	rm -f $(TARGET3).$(JS)
	rm -rf *~

.NOTPARALLEL: 

