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
const Moment = require('moment-mini');
const Logger = require('@accordproject/ergo-compiler').Logger;

require('yargs')
    .command('execute', 'execute an Ergo contract with a request', (yargs) => {
        yargs.demandOption(['contract', 'request'], 'Please provide at least the contract data and request');
        yargs.usage('Usage: $0 --contract [file] --state [file] --request [file] [ctos] [ergos]');
        yargs.option('contract', {
            describe: 'path to the contract data'
        });
        yargs.option('state', {
            describe: 'path to the state data',
            type: 'string',
            default: null
        });
        yargs.option('currentTime', {
            describe: 'the current time',
            type: 'string',
            default: Moment().format() // Defaults to now
        });
        yargs.option('request', {
            describe: 'path to the request data'
        }).array('request');
        yargs.option('warnings', {
            describe: 'print warnings',
            type: 'boolean',
            default: false
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
            Logger.info(`execute request to Ergo ${ergoPaths} over data ${argv.contract} with request ${argv.request}, state ${argv.state} and CTOs ${ctoPaths}`);
        }

        // Run contract
        Commands.execute(
            ergoPaths, ctoPaths, { file: argv.contract },
            argv.state ? { file: argv.state } : null,
            argv.currentTime, argv.request.map(r => { return { file: r }; }),
            argv.warnings)
            .then((result) => {
                Logger.info(JSON.stringify(result));
            })
            .catch((err) => {
                Logger.error(err.message);
            });
    })
    .command('invoke', 'invoke a clause for an Ergo contract', (yargs) => {
        yargs.demandOption(['clauseName', 'contract', 'state', 'params'], 'Please provide at least the clauseName, with contract data, state, and params');
        yargs.usage('Usage: $0 --contract [file] --state [file] --params [file] [ctos] [ergos]');
        yargs.option('clauseName', {
            describe: 'the name of the clause to invoke'
        });
        yargs.option('contract', {
            describe: 'path to the contract data'
        });
        yargs.option('state', {
            describe: 'path to the state data',
            type: 'string'
        });
        yargs.option('currentTime', {
            describe: 'the current time',
            type: 'string',
            default: Moment().format() // Defaults to now
        });
        yargs.option('params', {
            describe: 'path to the parameters',
            type: 'string',
            default: {}
        });
        yargs.option('template', {
            describe: 'path to the template (.tem) file',
            type: 'string',
            default: null
        });
        yargs.option('warnings', {
            describe: 'print warnings',
            type: 'boolean',
            default: false
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
        Commands.invoke(ergoPaths, ctoPaths, argv.clauseName, { file: argv.contract }, { file: argv.state }, argv.currentTime, { file: argv.params }, argv.template ? { file: argv.template } : null, argv.warnings)
            .then((result) => {
                Logger.info(JSON.stringify(result));
            })
            .catch((err) => {
                Logger.error(err.message);
            });
    })
    .command('init', 'invoke init for an Ergo contract', (yargs) => {
        yargs.demandOption(['contract'], 'Please provide at least contract and params');
        yargs.usage('Usage: $0 --contract [file] --params [file] [ctos] [ergos]');
        yargs.option('contract', {
            describe: 'path to the contract data'
        });
        yargs.option('currentTime', {
            describe: 'the current time',
            type: 'string',
            default: Moment().format() // Defaults to now
        });
        yargs.option('params', {
            describe: 'path to the parameters',
            type: 'string',
            default: null
        });
        yargs.option('warnings', {
            describe: 'print warnings',
            type: 'boolean',
            default: false
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
        Commands.init(ergoPaths, ctoPaths, { file: argv.contract }, argv.currentTime, argv.params ? { file: argv.params } : { content: '{}' }, argv.warnings)
            .then((result) => {
                Logger.info(JSON.stringify(result));
            })
            .catch((err) => {
                Logger.error(err.message);
            });
    })
    .command('generateText', 'invoke generateText for an Ergo contract', (yargs) => {
        yargs.demandOption(['contract'], 'Please provide at least the contract data');
        yargs.usage('Usage: $0 --contract [file] [ctos] [ergos]');
        yargs.option('contract', {
            describe: 'path to the contract data'
        });
        yargs.option('currentTime', {
            describe: 'the current time',
            type: 'string',
            default: Moment().format() // Defaults to now
        });
        yargs.option('markdown', {
            describe: 'generate with markdown notations',
            type: 'boolean',
            default: false
        });
        yargs.option('wrapVariables', {
            describe: 'wrap variables in curly braces',
            type: 'boolean',
            default: false
        });
        yargs.option('template', {
            describe: 'path to the template (.tem) file',
            type: 'string',
            default: null
        });
        yargs.option('warnings', {
            describe: 'print warnings',
            type: 'boolean',
            default: false
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
            Logger.info(`generateText for Ergo ${ergoPaths} over data ${argv.contract}`);
        }

        const options = {
            markdown: argv.markdown,
            wrapVariables: argv.wrapVariables,
        };
        // Generate text
        Commands.generateText(ergoPaths, ctoPaths, { file: argv.contract }, argv.currentTime, argv.template ? { file: argv.template } : null, options)
            .then((result) => {
                Logger.info(result.response);
            })
            .catch((err) => {
                Logger.error(err.message + '\n' + JSON.stringify(err));
            });
    })
    .option('verbose', {
        alias: 'v',
        default: false
    })
    .argv;
