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
const Ergo = require('@accordproject/ergo-compiler/lib/ergo');

try {
    const args = process.argv;
    const commonCTOs = Ergo.commonCTOs();
    for (let i = 0; i < commonCTOs.length; i++) {
        Logger.info();
        args.push(commonCTOs[i]);
    }
    for (let i = 0; i < args.length; i++) {
        if (args[i].split('.').pop() === 'cto') {
            const ctoPath = args[i];
            Commands.parseCTOtoFile(ctoPath);
            args[i] = ctoPath.substr(0, ctoPath.lastIndexOf('.')) + '.ctoj';
        }
    }
    //Logger.info(process.argv);
    require('../lib/ergoc-lib.js');
} catch (err) {
    Logger.info(err);
}
