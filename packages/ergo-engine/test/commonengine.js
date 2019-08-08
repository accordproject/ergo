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

const LogicManager = require('@accordproject/ergo-compiler').LogicManager;

const Chai = require('chai');
const expect = Chai.expect;

Chai.should();
Chai.use(require('chai-things'));
Chai.use(require('chai-as-promised'));

const Fs = require('fs');
const Path = require('path');

// Set of tests
const workload = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, 'workload.json'), 'utf8'));

/**
 * Compare actual and expected result components
 *
 * @param {string} expected the expected component as specified in the test workload
 * @param {string} actual the actual component as returned by the engine
 */
function compareComponent(expected,actual) {
    if (!expected) {
        expect(actual).to.equal(expected);
    } else {
        delete expected.timestamp;
        delete actual.timestamp;
        // Some basic deep comparison for arrays, since Chai doesn't do the right thing
        if (Array.isArray(actual)) {
            for (let i = 0; i < expected.length; i++) {
                delete expected[i].timestamp;
                delete actual[i].timestamp;
                expect(actual[i]).to.deep.include(expected[i]);
            }
        } else {
            expect(actual).to.deep.include(expected);
        }
    }
}

/**
 * Compare actual result and expected result
 *
 * @param {string} expected the expected successful result as specified in the test workload
 * @param {string} actual the successful result as returned by the engine
 */
function compareSuccess(expected,actual) {
    if (expected.hasOwnProperty('state')) {
        expect(actual).to.have.property('state');
        compareComponent(expected.state, actual.state);
    }
    if (expected.hasOwnProperty('response')) {
        expect(actual).to.have.property('response');
        compareComponent(expected.response, actual.response);
    }
    if (expected.hasOwnProperty('emit')) {
        expect(actual).to.have.property('emit');
        compareComponent(expected.emit, actual.emit);
    }
}

/**
 * Run a test workload
 *
 * @param {object} Engine - the engine class
 * @param {string} target - the target JS kind
 */
function runWorkload(Engine, target) {
    let engine = new Engine();
    let logicManager;

    beforeEach(async function () {
        engine = new Engine();
        logicManager = new LogicManager(target, null);
        logicManager.addErgoBuiltin();
    });

    afterEach(() => {});

    for (const i in workload) {
        const test = workload[i];
        const name = test.name;
        const dir = test.dir;
        const ergo = test.ergo;
        const models = test.models;
        const contract = test.contract;
        const state = test.state;
        const contractName = test.contractName;
        const currentTime = test.currentTime ? test.currentTime : '1970-01-01T00:00:00Z';
        const expected = test.expected;
        const options = test.options;

        let resultKind;
        if (expected.hasOwnProperty('compilationerror') || expected.hasOwnProperty('error')) {
            resultKind = 'fail';
        } else {
            resultKind = 'succeed';
        }

        describe('#'+name+' ('+engine.kind()+')', function () {
            it('should ' + resultKind + ' executing Ergo contract ' + contractName, async function () {
                for (let i = 0; i < ergo.length; i++) {
                    const ergoFile = Path.resolve(__dirname, dir, ergo[i]);
                    const ergoContent = Fs.readFileSync(ergoFile, 'utf8');
                    logicManager.addLogicFile(ergoContent, Path.join(dir, ergo[i]));
                }
                for (let i = 0; i < models.length; i++) {
                    const ctoFile = Path.resolve(__dirname, dir, models[i]);
                    const ctoContent = Fs.readFileSync(ctoFile, 'utf8');
                    logicManager.addModelFile(ctoContent, Path.join(dir, models[i]));
                }
                if (test.grammar) {
                    const templateFile = Path.resolve(__dirname, dir, test.grammar);
                    const templateContent = Fs.readFileSync(templateFile, 'utf8');
                    logicManager.addTemplateFile(templateContent, Path.join(dir, test.grammar));
                }
                logicManager.setContractName(contractName);
                const contractJson = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, dir, contract), 'utf8'));
                if (state === null) {
                    if (expected.hasOwnProperty('error')) {
                        return engine.compileAndInit(logicManager, contractJson, currentTime)
                            .catch((actualError) => {
                                expect(actualError.message).to.equal(expected.error);
                            });
                    } else {
                        return engine.compileAndInit(logicManager, contractJson, currentTime)
                            .then((actualAnswer) => {
                                return compareSuccess(expected, actualAnswer);
                            });
                    }
                } else {
                    if (test.clauseName) {
                        if (test.clauseName === 'generateText') {
                            if (expected.hasOwnProperty('error')) {
                                return engine.compileAndGenerateText(logicManager, contractJson, {}, currentTime, options)
                                    .catch((actualError) => {
                                        expect(actualError.message).to.equal(expected.error);
                                    });
                            } else {
                                return engine.compileAndGenerateText(logicManager, contractJson, {}, currentTime, options)
                                    .then((actualAnswer) => {
                                        return compareSuccess(expected, actualAnswer);
                                    });
                            }
                        } else {
                            const stateJson = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, dir, state), 'utf8'));
                            const params = test.params;
                            const clauseName = test.clauseName;
                            if (expected.hasOwnProperty('error')) {
                                return engine.compileAndInvoke(logicManager, clauseName, contractJson, params, stateJson, currentTime, options)
                                    .catch((actualError) => {
                                        expect(actualError.message).to.equal(expected.error);
                                    });
                            } else {
                                return engine.compileAndInvoke(logicManager, clauseName, contractJson, params, stateJson, currentTime, options)
                                    .then((actualAnswer) => {
                                        return compareSuccess(expected, actualAnswer);
                                    });
                            }
                        }
                    } else {
                        const stateJson = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, dir, state), 'utf8'));
                        const request = test.request;
                        const requestJson = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, dir, request), 'utf8'));
                        if (expected.hasOwnProperty('error')) {
                            return engine.compileAndExecute(logicManager, contractJson, requestJson, stateJson, currentTime, options)
                                .catch((actualError) => {
                                    expect(actualError.message).to.equal(expected.error);
                                });
                        } else {
                            return engine.compileAndExecute(logicManager, contractJson, requestJson, stateJson, currentTime, options)
                                .then((actualAnswer) => {
                                    return compareSuccess(expected, actualAnswer);
                                });
                        }
                    }
                }
            });
        });
    }
}

module.exports = { runWorkload };
