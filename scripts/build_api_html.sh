# install tools
npm install -g jsdoc

## Build the Ergo API

rm -rf ./website/static/ergo-api/
jsdoc -c ./scripts/ergo-jsdoc.conf -r ./ergo -d ./website/static/ergo-api/

