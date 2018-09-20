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
    .command('execute', 'execute Ergo contract', (yargs) => {
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
        yargs.option('ergo', {
            describe: 'paths to the Ergo sources'
        }).array('ergo');
        yargs.option('cto', {
            describe: 'path to CTO models'
        }).array('cto');
        yargs.option('contractname', {
            describe: 'contract name'
        });
    }, (argv) => {
        if (argv.verbose) {
            Logger.info(`execute Ergo contract ${argv.ergo} over data ${argv.contract} with request ${argv.request}  and state ${argv.state} and CTOs ${argv.cto}`);
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
