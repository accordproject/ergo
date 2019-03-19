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

const Engine = require('../lib/engine');
const Util = require('../lib/util');
const TemplateLogic = require('@accordproject/ergo-compiler').TemplateLogic;
const Chai = require('chai');
const expect = Chai.expect;

Chai.should();
Chai.use(require('chai-things'));
Chai.use(require('chai-as-promised'));

const Fs = require('fs');
const Path = require('path');

// Set of tests
const workload = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, 'workload.json'), 'utf8'));

describe('Execute ES6', () => {

    let engine;
    let templateLogic;
    beforeEach(async function () {
        engine = new Engine();
        templateLogic = new TemplateLogic('es6');
        templateLogic.addErgoBuiltin();
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
        let resultKind;
        if (expected.hasOwnProperty('compilationerror') || expected.hasOwnProperty('error')) {
            resultKind = 'fail';
        } else {
            resultKind = 'succeed';
        }

        describe('#'+name, function () {
            it('should ' + resultKind + ' executing Ergo contract ' + contractName, async function () {
                for (let i = 0; i < ergo.length; i++) {
                    const ergoFile = Path.resolve(__dirname, dir, ergo[i]);
                    const ergoContent = Fs.readFileSync(ergoFile, 'utf8');
                    templateLogic.addLogicFile(ergoContent, Path.join(dir, ergo[i]));
                }
                for (let i = 0; i < models.length; i++) {
                    const ctoFile = Path.resolve(__dirname, dir, models[i]);
                    const ctoContent = Fs.readFileSync(ctoFile, 'utf8');
                    templateLogic.addModelFile(ctoContent, Path.join(dir, models[i]));
                }
                templateLogic.setContractName(contractName);
                const contractJson = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, dir, contract), 'utf8'));
                if (state === null) {
                    if (expected.hasOwnProperty('error')) {
                        return engine.compileAndInit(templateLogic, contractName, contractJson, currentTime)
                            .catch((actualError) => {
                                expect(actualError.message).to.equal(expected.error);
                            });
                    } else {
                        return engine.compileAndInit(templateLogic, contractName, contractJson, currentTime)
                            .then((actualAnswer) => {
                                return Util.compareSuccess(expected, actualAnswer);
                            });
                    }
                } else {
                    const stateJson = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, dir, state), 'utf8'));
                    if (test.clauseName) {
                        const params = test.params;
                        const clauseName = test.clauseName;
                        if (expected.hasOwnProperty('error')) {
                            return engine.compileAndInvoke(templateLogic, contractName, clauseName, contractJson, params, stateJson, currentTime)
                                .catch((actualError) => {
                                    expect(actualError.message).to.equal(expected.error);
                                });
                        } else {
                            return engine.compileAndInvoke(templateLogic, contractName, clauseName, contractJson, params, stateJson, currentTime)
                                .then((actualAnswer) => {
                                    return Util.compareSuccess(expected, actualAnswer);
                                });
                        }
                    } else {
                        const request = test.request;
                        const requestJson = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, dir, request), 'utf8'));
                        if (expected.hasOwnProperty('error')) {
                            return engine.compileAndExecute(templateLogic, contractName, contractJson, requestJson, stateJson, currentTime)
                                .catch((actualError) => {
                                    expect(actualError.message).to.equal(expected.error);
                                });
                        } else {
                            return engine.compileAndExecute(templateLogic, contractName, contractJson, requestJson, stateJson, currentTime)
                                .then((actualAnswer) => {
                                    return Util.compareSuccess(expected, actualAnswer);
                                });
                        }
                    }
                }
            });
        });
    }
});
describe('Execute ES5', () => {

    let engine;
    let templateLogic;
    beforeEach(async function () {
        engine = new Engine();
        templateLogic = new TemplateLogic('es5');
        templateLogic.addErgoBuiltin();
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
        let resultKind;
        if (expected.hasOwnProperty('compilationerror') || expected.hasOwnProperty('error')) {
            resultKind = 'fail';
        } else {
            resultKind = 'succeed';
        }

        describe('#'+name, function () {
            it('should ' + resultKind + ' executing Ergo contract ' + contractName, async function () {
                for (let i = 0; i < ergo.length; i++) {
                    const ergoFile = Path.resolve(__dirname, dir, ergo[i]);
                    const ergoContent = Fs.readFileSync(ergoFile, 'utf8');
                    templateLogic.addLogicFile(ergoContent, Path.join(dir, ergo[i]));
                }
                for (let i = 0; i < models.length; i++) {
                    const ctoFile = Path.resolve(__dirname, dir, models[i]);
                    const ctoContent = Fs.readFileSync(ctoFile, 'utf8');
                    templateLogic.addModelFile(ctoContent, Path.join(dir, models[i]));
                }
                const contractJson = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, dir, contract), 'utf8'));
                if (state === null) {
                    if (expected.hasOwnProperty('error')) {
                        return engine.compileAndInit(templateLogic, contractName, contractJson, currentTime)
                            .catch((actualError) => {
                                expect(actualError.message).to.equal(expected.error);
                            });
                    } else {
                        return engine.compileAndInit(templateLogic, contractName, contractJson, currentTime)
                            .then((actualAnswer) => {
                                return Util.compareSuccess(expected, actualAnswer);
                            });
                    }
                } else {
                    const stateJson = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, dir, state), 'utf8'));
                    if (test.clauseName) {
                        const params = test.params;
                        const clauseName = test.clauseName;
                        if (expected.hasOwnProperty('error')) {
                            return engine.compileAndInvoke(templateLogic, contractName, clauseName, contractJson, params, stateJson, currentTime)
                                .catch((actualError) => {
                                    expect(actualError.message).to.equal(expected.error);
                                });
                        } else {
                            return engine.compileAndInvoke(templateLogic, contractName, clauseName, contractJson, params, stateJson, currentTime)
                                .then((actualAnswer) => {
                                    return Util.compareSuccess(expected, actualAnswer);
                                });
                        }
                    } else {
                        const request = test.request;
                        const requestJson = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, dir, request), 'utf8'));
                        if (expected.hasOwnProperty('error')) {
                            return engine.compileAndExecute(templateLogic, contractName, contractJson, requestJson, stateJson, currentTime)
                                .catch((actualError) => {
                                    expect(actualError.message).to.equal(expected.error);
                                });
                        } else {
                            return engine.compileAndExecute(templateLogic, contractName, contractJson, requestJson, stateJson, currentTime)
                                .then((actualAnswer) => {
                                    return Util.compareSuccess(expected, actualAnswer);
                                });
                        }
                    }
                }
            });
        });
    }
});
