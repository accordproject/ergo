npm install -g jsdoc-to-markdown

## Build the Ergo API
jsdoc2md -c ./scripts/ergo-jsdoc.conf --files ./packages/**/*.js > ./docs/ergo-api.md
jsdoc2md --template ./scripts/ergo-api.hbs -c ./scripts/ergo-jsdoc.conf --files ./packages/**/*.js > ./docs/ergo-api.md
