# install tools
npm install -g jsdoc

## Build the Ergo API

rm -rf ./website/static/ergo-api-js/
jsdoc -c ./scripts/ergo-jsdoc.conf -r ./ergo -d ./website/static/ergo-api-js/

