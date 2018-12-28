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
const Path = require('path');

const Chai = require('chai');
const expect = Chai.expect;

const ErgoEngine = require('../../../lib/ergo-engine');

const { Given, When, Then } = require('cucumber');

const defaultState = {'stateId':'1','$class':'org.accordproject.cicero.contract.AccordContractState'};

/**
 * Compare actual result and expected result
 *
 * @param {string} expected the result as specified in the test workload
 * @param {string} actual the result as returned by the engine
 */
function compare(expected,actual) {
    for (const key in expected) {
        if (expected.hasOwnProperty(key)) {
            const field = key;
            const value = expected[key];
            expect(actual).to.have.property(field);
            expect(actual[field]).to.deep.equal(value);
        }
    }
}

/**
 * Calls Ergo contract initialization
 *
 * @param {Array<string>} ergo the list of ergo files
 * @param {Array<string>} models the list of model files
 * @param {string} contractname the fully qualified name of the contract
 * @param {object} contractJson contract data in JSON
 * @returns {object} Promise to the initial state of the contract
 */
async function init(ergo,models,contractname,contractJson) {
    const ergoSources = [];
    for (let i = 0; i < ergo.length; i++) {
        const ergoFile = Path.resolve(__dirname, '..', '..', ergo[i]);
        const ergoContent = Fs.readFileSync(ergoFile, 'utf8');
        ergoSources.push({ 'name': ergoFile, 'content': ergoContent });
    }
    let ctoSources = [];
    for (let i = 0; i < models.length; i++) {
        const ctoFile = Path.resolve(__dirname, '..', '..', models[i]);
        const ctoContent = Fs.readFileSync(ctoFile, 'utf8');
        ctoSources.push({ 'name': ctoFile, 'content': ctoContent });
    }
    const requestJson = { '$class' : 'org.accordproject.cicero.runtime.Request' };
    return ErgoEngine.init(ergoSources, ctoSources, 'es6', contractJson, requestJson, contractname);
}

/**
 * Sends a request to the Ergo contract
 *
 * @param {Array<string>} ergo the list of ergo files
 * @param {Array<string>} models the list of model files
 * @param {string} contractname the fully qualified name of the contract
 * @param {object} contractJson contract data in JSON
 * @param {object} stateJson state data in JSON
 * @param {object} requestJson state data in JSON
 * @returns {object} Promise to the response
 */
async function send(ergo,models,contractname,contractJson,stateJson,requestJson) {
    const ergoSources = [];
    for (let i = 0; i < ergo.length; i++) {
        const ergoFile = Path.resolve(__dirname, '..', '..', ergo[i]);
        const ergoContent = Fs.readFileSync(ergoFile, 'utf8');
        ergoSources.push({ 'name': ergoFile, 'content': ergoContent });
    }
    let ctoSources = [];
    for (let i = 0; i < models.length; i++) {
        const ctoFile = Path.resolve(__dirname, '..', '..', models[i]);
        const ctoContent = Fs.readFileSync(ctoFile, 'utf8');
        ctoSources.push({ 'name': ctoFile, 'content': ctoContent });
    }
    let actualStateJson;
    if (stateJson) {
        actualStateJson = stateJson;
    } else {
        actualStateJson = defaultState;
    }
    return ErgoEngine.execute(ergoSources, ctoSources, 'es6', contractJson, requestJson, actualStateJson, contractname);
}

Given('the Ergo contract {string} in file {string}', function(paramName,paramFile) {
    if (this.ergos) {
        this.ergos.push(paramFile);
        this.contractname = paramName;
    } else {
        this.ergos = [paramFile];
        this.contractname = paramName;
    }
});

Given('the Ergo logic in file {string}', function(paramFile) {
    if (this.ergos) {
        this.ergos.push(paramFile);
    } else {
        this.ergos = [paramFile];
    }
});

Given('the model in file {string}', function(paramFile) {
    if (this.models) {
        this.models.push(paramFile);
    } else {
        this.models = [paramFile];
    }
});

Given('the contract data', function (actualContract) {
    this.contract = JSON.parse(actualContract);
});

When('it is in the state', function (actualState) {
    this.state = JSON.parse(actualState);
});

When('it receives the request', function (actualRequest) {
    this.request = JSON.parse(actualRequest);
});

Then('it should respond with', function (expectedResponse) {
    const response = JSON.parse(expectedResponse);
    if (this.answer) {
        expect(this.answer).to.have.property('response');
        expect(this.answer).to.not.have.property('error');
        return compare(response,this.answer.response);
    } else {
        return send(this.ergos,this.models,this.contractname,this.contract,this.state,this.request)
            .then((actualAnswer) => {
                this.answer = actualAnswer;
                expect(actualAnswer).to.have.property('response');
                expect(actualAnswer).to.not.have.property('error');
                return compare(response,actualAnswer.response);
            });
    }
});

Then('the initial state( of the contract) should be', function (expectedState) {
    const state = JSON.parse(expectedState);
    return init(this.ergos,this.models,this.contractname,this.contract)
        .then((actualAnswer) => {
            expect(actualAnswer).to.have.property('state');
            expect(actualAnswer).to.not.have.property('error');
            return compare(state,actualAnswer.state);
        });
});

Then('the initial state( of the contract) should be the default state', function () {
    const state = defaultState;
    return init(this.ergos,this.models,this.contractname,this.contract)
        .then((actualAnswer) => {
            expect(actualAnswer).to.have.property('state');
            expect(actualAnswer).to.not.have.property('error');
            return compare(state,actualAnswer.state);
        });
});

Then('the new state( of the contract) should be', function (expectedState) {
    const state = JSON.parse(expectedState);
    if (this.answer) {
        expect(this.answer).to.have.property('state');
        expect(this.answer).to.not.have.property('error');
        return compare(state,this.answer.state);
    } else {
        return send(this.ergos,this.models,this.contractname,this.contract,this.state,this.request)
            .then((actualAnswer) => {
                this.answer = actualAnswer;
                expect(actualAnswer).to.have.property('state');
                expect(actualAnswer).to.not.have.property('error');
                return compare(state,actualAnswer.state);
            });
    }
});

Then('it should fail with the error', function (expectedError) {
    const error = JSON.parse(expectedError);
    if (this.answer) {
        expect(this.answer).to.have.property('error');
        expect(this.answer).to.not.have.property('state');
        expect(this.answer).to.not.have.property('response');
        return compare(error,this.answer.error);
    } else {
        return send(this.ergos,this.models,this.contractname,this.contract,this.state,this.request)
            .then((actualAnswer) => {
                this.answer = actualAnswer;
                expect(actualAnswer).to.have.property('error');
                expect(actualAnswer).to.not.have.property('state');
                expect(actualAnswer).to.not.have.property('response');
                return compare(error,actualAnswer.error);
            });
    }
});

Then('it should fail to initialize with the error', function (expectedError) {
    const error = JSON.parse(expectedError);
    return init(this.ergos,this.models,this.contractname,this.contract)
        .then((actualAnswer) => {
            expect(actualAnswer).to.have.property('error');
            expect(actualAnswer).to.not.have.property('state');
            expect(actualAnswer).to.not.have.property('response');
            return compare(error,actualAnswer.error);
        });
});

