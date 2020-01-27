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

###
### WARNING: This file is meant to be invoked by the ergo/Makefile documentation target, not run directly
###

include ../../Makefile.coq_modules

COQ_FILES = $(MODULES:%=%.v)
GLOB_FILES = $(MODULES:%=%.glob)
TECHDOCS=../../../techdocs

documentation: $(GLOB_FILES) $(COQ_FILES)
	mkdir -p $(TECHDOCS)/docs/assets/specification
	rm -f $(TECHDOCS)/docs/assets/specification/*.html
	coq2html -d $(TECHDOCS)/docs/assets/specification -external https://querycert.github.io/html Qcert -base ErgoSpec $^

.PHONY: documentation
