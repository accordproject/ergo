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

const ergotop = require('../lib/ergotop.js').ergotop;
const readline = require('readline');
const rl = readline.createInterface({
    input: process.stdin,
    output: process.stdout
});

let ctx = ergotop.initRCtxt;

/** Does the thing
 * @param {string} line - the line */
function run(line) {
    const x = ergotop.runLine(ctx, line);
    if (x) {
        ctx = x.ctx;
        process.stdout.write(x.out + '\n');
    }
    rl.question('ergo$ ', run);
}

run('');
