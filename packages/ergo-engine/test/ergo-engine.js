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

const ErgoEngine = require('../lib/ergo-engine');
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
        const ergo = test.ergo;
        const models = test.models;
        const contract = test.contract;
        const request = test.request;
        const state = test.state;
        const contractname = test.contractname;
        const clausename = test.clausename;
        const expected = test.expected;
        let resultKind;
        if (expected.error) {
            resultKind = 'fail';
        } else {
            resultKind = 'succeed';
        }

        describe('#execute'+name, function () {
            it('should ' + resultKind + ' executing Ergo clause ' + clausename + ' in contract ' + contractname, async function () {
                const ergoText = Fs.readFileSync(Path.resolve(__dirname, dir, ergo), 'utf8');
                let ctoTexts = [];
                for (let i = 0; i < models.length; i++) {
                    ctoTexts.push(Fs.readFileSync(Path.resolve(__dirname, dir, models[i]), 'utf8'));
                }
                const clauseJson = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, dir, contract), 'utf8'));
                const requestJson = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, dir, request), 'utf8'));
                const stateJson = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, dir, state), 'utf8'));
                if (expected.error) {
                    const result = ErgoEngine.execute(ergoText, ctoTexts, clauseJson, requestJson, stateJson, contractname, clausename, false);
                    return result.catch(function(m) { m.should.deep.equal(new Error(expected.error)); });
                } else {
                    const result = await ErgoEngine.execute(ergoText, ctoTexts, clauseJson, requestJson, stateJson, contractname, clausename, false);
                    for (const key in expected) {
                        if (expected.hasOwnProperty(key)) {
                            const field = key;
                            const value = expected[key];
                            //result.should.not.be.null;
                            result.response[field].should.equal(value);
                        }
                    }
                }
            });
        });
    }
});
