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

const Fs = require('fs');
const CTOParser = require('@accordproject/concerto/lib/introspect/parser');

require('yargs')
    .command('parse', 'parse CTO file to JSON', (yargs) => {
    }, (argv) => {
        const files = argv._.slice(1);
        for (let i = 0; i < files.length; i++) {
            try {
                const inFile = files[i];
                console.info(`Parsing CTO '${inFile}'`);
                const ctoText = Fs.readFileSync(inFile, 'utf8');
                const ctoJson = CTOParser.parse(ctoText);
                const outFile = inFile.substr(0, inFile.lastIndexOf('.')) + '.ctoj';
                Fs.writeFileSync(outFile, JSON.stringify(ctoJson));
                console.info(`Create CTOJ file ${outFile}`);
            } catch (err) {
                console.error(err.message + ' ' + JSON.stringify(err));
            };
        }
    })
    .demandCommand()
    .option('verbose', {
        alias: 'v',
        default: false
    })
    .argv;
