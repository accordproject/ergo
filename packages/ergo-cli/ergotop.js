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
const Logger = require('@accordproject/ergo-compiler').Logger;

try {
    const args = process.argv;
    for (let i = 0; i < args.length; i++) {
        if (args[i].split('.').pop() === 'cto') {
            const ctoPath = args[i];
            Commands.parseCTOtoFile(ctoPath);
            args[i] = ctoPath.substr(0, ctoPath.lastIndexOf('.')) + '.ctoj';
        }
    }

    const ergotop = require('./extracted/ergotopcore.js').ergotop;
    const readline = require('readline');
    const chalk = require('chalk');

    const PS1 = chalk.gray('ergo$ ');
    const PS2 = chalk.gray('  ... ');
    const rl = readline.createInterface({
        input: process.stdin,
        output: process.stdout,
        prompt: PS1
    });

    let ctx = ergotop.initRCtxt;
    let inp = '';

    rl.on('line', (line) => {
        if (line.charAt(line.length - 1) === '\\') {
            inp += line.slice(0, line.length - 1) + '\n';
            rl.setPrompt(PS2);
        } else {
            inp += line + '\n';
            rl.setPrompt(PS1);
            const x = ergotop.runLine(ctx, inp);
            inp = '';
            if (x) {
                ctx = x.ctx;
                process.stdout.write(
                    x.out
                        .replace(/^Response. /gm, chalk.green('Response. '))
                        .replace(/^Emit. /gm, chalk.magenta('Emit. '))
                        .replace(/^State. /gm, chalk.blue('State. '))
                        .replace(/^Failure. /gm, chalk.red('Failure. '))
                );
            }
        }
        rl.prompt();
    }).on('close', () => {
        process.exit(0);
    });

    rl.prompt();
} catch (err) {
    Logger.error(err.message);
}
