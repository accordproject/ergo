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
const Logger = require('../lib/logger');

require('yargs')
    .command('parse', 'parse CTO file to JSON', (yargs) => {
        yargs.option('cto', {
            describe: 'path to the CTO file'
        });
    }, (argv) => {
        if (argv.verbose) {
            Logger.info(`parse CTO file ${argv.cto}`);
        }
        return Commands.parseCTO(argv.cto)
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
