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
const Logger = require('@accordproject/ergo-compiler/lib/logger');

require('yargs')
    .command('compile', 'compile Ergo to JavaScript', (yargs) => {
        yargs.option('ergo', {
            describe: 'path to the Ergo source'
        });
        yargs.option('cto', {
            describe: 'path to CTO models'
        }).array('cto');
        yargs.option('target', {
            describe: 'target language (javascript|javascript_cicero)',
            type: 'string',
            default: 'javascript'
        });
        yargs.option('link', {
            describe: 'link to JavaScript runtime',
            type: 'boolean',
            default: false
        });
    }, (argv) => {
        if (argv.verbose) {
            Logger.info(`compile Ergo file ${argv.ergo} and CTOs ${argv.cto}`);
        }
        return Commands.compile(argv.ergo,argv.cto,argv.target,argv.link)
            .then((result) => {
                Logger.info(result);
            })
            .catch((err) => {
                Logger.error(err.message + ' ' + JSON.stringify(err));
            });
    })
    .command('execute', 'execute a contract', (yargs) => {
        yargs.option('contract', {
            describe: 'path to the contract data'
        });
        yargs.option('request', {
            describe: 'path to the request data'
        }).array('request');
        yargs.option('state', {
            describe: 'path to the state data'
        });
        yargs.option('ergo', {
            describe: 'path to the Ergo file'
        });
        yargs.option('cto', {
            describe: 'path to CTO models'
        }).array('cto');
        yargs.option('contractname', {
            describe: 'contract name'
        });
    }, (argv) => {
        if (argv.verbose) {
            Logger.info(`execute Ergo file ${argv.ergo} on contract data ${argv.contract} with request data ${argv.request} and CTOs ${argv.cto}`);
        }

        return Commands.execute(argv.ergo, argv.cto, argv.contract, argv.request, argv.state, argv.contractname)
            .then((result) => {
                Logger.info(JSON.stringify(result));
            })
            .catch((err) => {
                Logger.error(err.message + ' ' + JSON.stringify(err));
            });
    })
    .demandCommand()
    .option('verbose', {
        alias: 'v',
        default: false
    })
    .argv;
