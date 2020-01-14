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

## Toplevel
all: ./ErgoComp.ml

## Extraction
VO_FILES = $(MODULES:%=../core/%.vo)

./ErgoComp.ml ./ErgoComp.mli: $(VO_FILES)
ifneq ($(QCERT),)
	(coqc -R ../core ErgoSpec -R ../../$(QCERT)/compiler/core Qcert ./ErgoExtraction.v)
else
	(coqc -R ../core ErgoSpec ./ErgoExtraction.v)
endif

## Clean

clean:

cleanall: clean
	rm -f ErgoExtraction.glob ErgoExtraction.vo .ErgoExtraction.aux
	rm -rf ErgoComp.ml ErgoComp.mli
	rm -rf *~

.NOTPARALLEL: 

