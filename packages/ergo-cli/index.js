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

const Commands = require('./lib/commands');
const Moment = require('moment-mini');
const Logger = require('@accordproject/ergo-compiler').Logger;

require('yargs')
    .scriptName('ergo')
    .demandCommand(1, '# Please specify a command')
    .recommendCommands()
    .strict()
    .command('trigger', 'send a request to the contract', (yargs) => {
        yargs.demandOption(['data', 'request'], 'Please provide at least the contract data and a request');
        yargs.usage('Usage: $0 trigger --data [file] --state [file] --request [file] --target [lang] [cto files] [ergo files]');
        yargs.option('data', {
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
        yargs.option('template', {
            describe: 'path to the template directory',
            type: 'string',
            default: null
        });
        yargs.option('target', {
            describe: 'Target platform (available: es6,java,wasm)',
            type: 'string',
            default: 'es6'
        });
        yargs.option('warnings', {
            describe: 'print warnings',
            type: 'boolean',
            default: false
        });
    }, (argv) => {
        let files = argv._;

        if (argv.verbose) {
            Logger.info(`send request ${argv.request} for contract data ${argv.data}`);
        }

        // Run contract
        Commands.trigger(argv.template, files, { file: argv.data }, argv.state ? { file: argv.state } : null,
            argv.currentTime, argv.request.map(r => { return { file: r }; }), argv.warnings, argv.target)
            .then((result) => {
                Logger.info(JSON.stringify(result));
            })
            .catch((err) => {
                Logger.error(err);
            });
    })
    .command('invoke', 'invoke a clause of the contract', (yargs) => {
        yargs.demandOption(['clauseName', 'data', 'state', 'params'], 'Please provide at least the clauseName, with contract data, state, and parameters');
        yargs.usage('Usage: $0 invoke --data [file] --state [file] --params [file] --target [lang] [cto files] [ergo files]');
        yargs.option('clauseName', {
            describe: 'the name of the clause to invoke'
        });
        yargs.option('data', {
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
            describe: 'path to the template directory',
            type: 'string',
            default: null
        });
        yargs.option('target', {
            describe: 'Target platform (available: es6,java,wasm)',
            type: 'string',
            default: 'es6'
        });
        yargs.option('warnings', {
            describe: 'print warnings',
            type: 'boolean',
            default: false
        });
    }, (argv) => {
        let files = argv._;

        if (argv.verbose) {
            Logger.info(`invoke clause ${argv.clauseName} in contract`);
        }

        // Run contract
        Commands.invoke(argv.template, files, argv.clauseName, { file: argv.data }, { file: argv.state }, argv.currentTime, { file: argv.params }, argv.warnings, argv.target)
            .then((result) => {
                Logger.info(JSON.stringify(result));
            })
            .catch((err) => {
                Logger.error(err.message);
            });
    })
    .command('initialize', 'initialize the state for a contract', (yargs) => {
        yargs.demandOption(['data'], 'Please provide at least contract data and parameters');
        yargs.usage('Usage: $0 intialize --data [file] --params [file] --target [lang] [cto files] [ergo files]');
        yargs.option('data', {
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
        yargs.option('template', {
            describe: 'path to the template directory',
            type: 'string',
            default: null
        });
        yargs.option('target', {
            describe: 'Target platform (available: es6,java,wasm)',
            type: 'string',
            default: 'es6'
        });
        yargs.option('warnings', {
            describe: 'print warnings',
            type: 'boolean',
            default: false
        });
    }, (argv) => {
        let files = argv._;

        if (argv.verbose) {
            Logger.info(`initialize contract state with data ${argv.data}`);
        }

        // Run contract
        Commands.initialize(argv.template, files, { file: argv.data }, argv.currentTime, argv.params ? { file: argv.params } : { content: '{}' }, argv.warnings, argv.target)
            .then((result) => {
                Logger.info(JSON.stringify(result));
            })
            .catch((err) => {
                Logger.error(err.message);
            });
    })
    .command('compile', 'compile a contract', (yargs) => {
        yargs.usage('Usage: $0 compile --target [lang] --link --monitor --warnings [cto files] [ergo files]');
        yargs.option('target', {
            describe: 'Target platform (available: es6,java,wasm)',
            type: 'string',
            default: 'es6'
        });
        yargs.option('link', {
            describe: 'Link the Ergo runtime with the target code (es6 only)',
            type: 'boolean',
            default: false
        });
        yargs.option('monitor', {
            describe: 'Produce compilation time information',
            type: 'boolean',
            default: false
        });
        yargs.option('warnings', {
            describe: 'print warnings',
            type: 'boolean',
            default: false
        });
    }, (argv) => {
        try {
            // Removes the `compile`
            const args = [process.argv[0],process.argv[1]].concat(process.argv.slice(3));
            for (let i = 0; i < args.length; i++) {
                if (args[i].split('.').pop() === 'cto') {
                    const ctoPath = args[i];
                    Commands.parseCTOtoFile(ctoPath);
                    args[i] = ctoPath.substr(0, ctoPath.lastIndexOf('.')) + '.ctoj';
                }
            }
            process.argv = args;
            require('./extracted/ergoccore.js');
        } catch (err) {
            Logger.error(err.message);
        }
    })
    .option('verbose', {
        alias: 'v',
        default: false
    })
    .argv;
