#!/usr/bin/env node
const Jura = require('../lib/jura');

require('yargs')
    .command('parse', 'parse CTO file to JSON', (yargs) => {
        yargs.option('cto', {
            describe: 'path to the CTO file'
        });
    }, (argv) => {
        if (argv.verbose) {
            console.log(`parse CTO file ${argv.cto}`);
        }
        return Jura.parseCTO(argv.cto)
            .then((result) => {
                console.log(JSON.stringify(result));
            })
            .catch((err) => {
                console.error(err.message + ' ' + JSON.stringify(err));
            });
    })
    .demandCommand()
    .option('verbose', {
        alias: 'v',
        default: false
    })
    .argv;
