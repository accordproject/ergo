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

PDF2SVG=pdf2svg

all: frontend.pdf frontend.svg frontend.png

%.svg.gen: %.dvi
	dvisvgm $< -o "%f.svg.gen"

node_modules:
	npm install

%.js %.js.map: %.ts node_modules
	./node_modules/.bin/tsc

%.svg: %.svg.gen cleansvg.js
	node ./cleansvg.js $< > $@

%.png: %.pdf
	convert $< $@

%.pdf: %.tex frontend-coq.tex tikzmacros.tex
	pdflatex --shell-escape $<
	pdflatex --shell-escape $<
	pdflatex --shell-escape $<

%.dvi: %.tex frontend-coq.tex tikzmacros.tex
	latex $<
	latex $<

clean:
	rm -f *~ frontend.out frontend.log frontend.aux frontend.dvi frontend.svg.gen frontend.lg frontend.js frontend.js.map

cleanall: clean
	rm -f frontend.pdf frontend.png frontend.svg

cleandist: cleanall
	rm -rf node_modules

PRECIOUS: *.gen.svg *.dvi
