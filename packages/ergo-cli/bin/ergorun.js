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
const Moment = require('moment');
const Logger = require('@accordproject/ergo-compiler/lib/logger');

require('yargs')
    .command('send', 'send a request to an Ergo contract', (yargs) => {
        yargs.demandOption(['contract', 'request', 'contractName', 'currentTime'], 'Please provide at least contract, request and contractName');
        yargs.usage('Usage: $0 --contract [file] --state [file] --request [file] [ctos] [ergos]');
        yargs.option('contract', {
            describe: 'path to the contract data'
        });
        yargs.option('request', {
            describe: 'path to the request data'
        }).array('request');
        yargs.option('state', {
            describe: 'path to the state data',
            type: 'string',
            default: null
        });
        yargs.option('contractName', {
            describe: 'the name of the contract'
        });
        yargs.option('currentTime', {
            describe: 'the current time',
            type: 'string',
            default: Moment().format() // Defaults to now
        });
        yargs.option('state', {
            describe: 'path to the state data',
            type: 'string',
            default: null
        });
    }, (argv) => {
        let ctoPaths = [];
        let ergoPaths = [];

        const files = argv._;
        for (let i = 0; i < files.length; i++) {
            const file = files[i];
            if (file.split('.').pop() === 'cto') {
                //Logger.info('Found CTO: ' + file);
                ctoPaths.push(file);
            } else if (file.split('.').pop() === 'ergo') {
                //Logger.info('Found Ergo: ' + file);
                ergoPaths.push(file);
            }
        }

        if (argv.verbose) {
            Logger.info(`send request to Ergo ${ergoPaths} over data ${argv.contract} with request ${argv.request}, state ${argv.state} and CTOs ${ctoPaths}`);
        }

        // Run contract
        Commands.send(ergoPaths, ctoPaths, argv.contract, argv.request, argv.state, argv.contractName, argv.currentTime)
            .then((result) => {
                Logger.info(JSON.stringify(result));
            })
            .catch((err) => {
                Logger.error(err.message + ' ' + JSON.stringify(err));
            });
    })
    .command('invoke', 'invoke a clause for an Ergo contract', (yargs) => {
        yargs.demandOption(['contract', 'params', 'state', 'contractName', 'clauseName', 'currentTime'], 'Please provide at least contract, params, state, contractName and clauseName');
        yargs.usage('Usage: $0 --contract [file] --state [file] --params [file] [ctos] [ergos]');
        yargs.option('contract', {
            describe: 'path to the contract data'
        });
        yargs.option('params', {
            describe: 'path to the parameters',
            type: 'string',
            default: {}
        });
        yargs.option('state', {
            describe: 'path to the state data',
            type: 'string',
            default: null
        });
        yargs.option('contractName', {
            describe: 'the name of the contract'
        });
        yargs.option('clauseName', {
            describe: 'the name of the clause to invoke'
        });
        yargs.option('currentTime', {
            describe: 'the current time',
            type: 'string',
            default: Moment().format() // Defaults to now
        });
        yargs.option('state', {
            describe: 'path to the state data',
            type: 'string',
            default: null
        });
    }, (argv) => {
        let ctoPaths = [];
        let ergoPaths = [];

        const files = argv._;
        for (let i = 0; i < files.length; i++) {
            const file = files[i];
            if (file.split('.').pop() === 'cto') {
                //Logger.info('Found CTO: ' + file);
                ctoPaths.push(file);
            } else if (file.split('.').pop() === 'ergo') {
                //Logger.info('Found Ergo: ' + file);
                ergoPaths.push(file);
            }
        }

        if (argv.verbose) {
            Logger.info(`call Ergo ${ergoPaths} over data ${argv.contract} with params ${argv.params}, state ${argv.state} and CTOs ${ctoPaths}`);
        }

        // Run contract
        Commands.invoke(ergoPaths, ctoPaths, argv.contract, argv.params, argv.state, argv.contractName, argv.clauseName, argv.currentTime)
            .then((result) => {
                Logger.info(JSON.stringify(result));
            })
            .catch((err) => {
                Logger.error(err.message + ' ' + JSON.stringify(err));
            });
    })
    .command('init', 'invoke init for an Ergo contract', (yargs) => {
        yargs.demandOption(['contract', 'params', 'contractName', 'clauseName', 'currentTime'], 'Please provide at least contract, params and contractName');
        yargs.usage('Usage: $0 --contract [file] --params [file] [ctos] [ergos]');
        yargs.option('contract', {
            describe: 'path to the contract data'
        });
        yargs.option('params', {
            describe: 'path to the parameters',
            type: 'string',
            default: {}
        });
        yargs.option('contractName', {
            describe: 'the name of the contract'
        });
        yargs.option('currentTime', {
            describe: 'the current time',
            type: 'string',
            default: Moment().format() // Defaults to now
        });
        yargs.option('state', {
            describe: 'path to the state data',
            type: 'string',
            default: null
        });
    }, (argv) => {
        let ctoPaths = [];
        let ergoPaths = [];

        const files = argv._;
        for (let i = 0; i < files.length; i++) {
            const file = files[i];
            if (file.split('.').pop() === 'cto') {
                //Logger.info('Found CTO: ' + file);
                ctoPaths.push(file);
            } else if (file.split('.').pop() === 'ergo') {
                //Logger.info('Found Ergo: ' + file);
                ergoPaths.push(file);
            }
        }

        if (argv.verbose) {
            Logger.info(`init Ergo ${ergoPaths} over data ${argv.contract} with params ${argv.params} and CTOs ${ctoPaths}`);
        }

        // Run contract
        Commands.init(ergoPaths, ctoPaths, argv.contract, argv.params, argv.contractName, argv.currentTime)
            .then((result) => {
                Logger.info(JSON.stringify(result));
            })
            .catch((err) => {
                Logger.error(err.message + ' ' + JSON.stringify(err));
            });
    })
    .option('verbose', {
        alias: 'v',
        default: false
    })
    .argv;
