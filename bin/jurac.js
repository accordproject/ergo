#!/usr/bin/env node
/*
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

'use strict';

const Commands = require('../lib/commands');

require('yargs')
    .command('compile', 'compile Jura to JavaScript', (yargs) => {
        yargs.option('jura', {
            describe: 'path to the Jura source'
        });
        yargs.option('contractname', {
            describe: 'contract name'
        });
        yargs.option('clausename', {
            describe: 'clause name'
        });
        yargs.option('dispatch', {
            describe: 'generate dispatch function',
	    type: 'boolean',
	    default: false
        });
    }, (argv) => {
        if (argv.verbose) {
            console.log(`compile Jura file ${argv.jura} with contract ${argv.contractname} and clause with contract ${argv.clausename}`);
        }
        return Commands.compile(argv.jura,argv.contractname,argv.clausename, argv.dispatch)
            .then((result) => {
                console.log(result);
            })
            .catch((err) => {
                console.error(err.message + ' ' + JSON.stringify(err));
            });
    })
    .command('execute', 'execute a contract clause', (yargs) => {
        yargs.option('clause', {
            describe: 'path to the clause data'
        });
        yargs.option('request', {
            describe: 'path to the request data'
        });
        yargs.option('jura', {
            describe: 'path to the Jura file'
        });
        yargs.option('contractname', {
            describe: 'contract name'
        });
        yargs.option('clausename', {
            describe: 'clause name'
        });
        yargs.option('dispatch', {
            describe: 'generate dispatch function',
	    type: 'boolean',
	    default: false
        });
    }, (argv) => {
        if (argv.verbose) {
            console.log(`execute Jura clause ${argv.jura} using clause data ${argv.clause} with request data ${argv.request}`);
        }

        return Commands.execute(argv.jura, argv.clause, argv.request, argv.contractname, argv.clausename, argv.dispatch)
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
