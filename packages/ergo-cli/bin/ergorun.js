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

const argv =
    require('yargs')
        .demandOption(['contract', 'request', 'contractName'], 'Please provide at least contract, request and contractName')
        .usage('Usage: $0 --contract [file] --state [file] --request [file] [ctos] [ergos]')
        .option('contract', {
            describe: 'path to the contract data'
        })
        .option('request', {
            describe: 'path to the request data'
        }).array('request')
        .option('state', {
            describe: 'path to the state data',
            type: 'string',
            default: null
        })
        .option('contractName', {
            describe: 'the name of the contract to run'
        })
        .option('currentTime', {
            describe: 'the current time',
            type: 'string',
            default: null
        })
        .option('state', {
            describe: 'path to the state data',
            type: 'string',
            default: null
        })
        .option('verbose', {
            alias: 'v',
            default: false
        })
        .argv
;

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
    Logger.info(`execute Ergo ${ergoPaths} over data ${argv.contract} with request ${argv.request}, state ${argv.state} and CTOs ${ctoPaths}`);
}

// Run contract
Commands.execute(ergoPaths, ctoPaths, argv.contract, argv.request, argv.state, argv.contractName, argv.currentTime)
    .then((result) => {
        Logger.info(JSON.stringify(result));
    })
    .catch((err) => {
        Logger.error(err.message + ' ' + JSON.stringify(err));
    });
