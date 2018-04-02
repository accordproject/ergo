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

const JuraEngine = require('../lib/jura-engine');
const Chai = require('chai');

Chai.should();
Chai.use(require('chai-things'));

const Fs = require('fs');
const Path = require('path');

// Set of tests
const workload = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, 'workload.json'), 'utf8'));

describe('Execute', () => {

    afterEach(() => {});

    for (const i in workload) {
        const test = workload[i];
        const name = test.name;
        const dir = test.dir;
        const jura = test.jura;
        const model = test.model;
        const contract = test.contract;
        const request = test.request;
        const state = test.state;
        const contractname = test.contractname;
        const clausename = test.clausename;
        const expected = test.expected;

        describe('#execute'+name, function () {
            it('should execute Jura clause ' + clausename + ' in contract ' + contractname, async function () {
                const juraText = Fs.readFileSync(Path.resolve(__dirname, dir, jura), 'utf8');
                const ctoText = Fs.readFileSync(Path.resolve(__dirname, dir, model), 'utf8');
                const clauseJson = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, dir, contract), 'utf8'));
                const requestJson = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, dir, request), 'utf8'));
                const stateJson = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, dir, state), 'utf8'));
                const result = await JuraEngine.execute(juraText, ctoText, clauseJson, requestJson, stateJson, contractname, clausename, false);
                //console.log(JSON.stringify(result));
                for (const key in expected) {
                    if (expected.hasOwnProperty(key)) {
                        const field = key;
                        const value = expected[key];
                        //result.should.not.be.null;
                        result.response[field].should.equal(value);
                    }
                }
            });
        });
    }
});
