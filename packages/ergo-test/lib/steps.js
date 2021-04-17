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

const LogicManager = require('@accordproject/ergo-compiler').LogicManager;
const Engine = require('@accordproject/ergo-engine').VMEngine;
const Util = require('./util');

const { Before, Given, When, Then } = require('cucumber');

// Defaults
const defaultState = {
    '$class':'org.accordproject.runtime.State'
};

/**
 * Invoke Ergo contract initialization
 *
 * @param {object} engine - the execution engine
 * @param {object} logicManager - the Template Logic
 * @param {object} contractJson - contract data in JSON
 * @param {string} currentTime - the definition of 'now'
 * @param {utcOffset} utcOffset - UTC Offset for this execution
 * @returns {object} Promise to the initial state of the contract
 */
function init(engine,logicManager,contractJson,currentTime,utcOffset) {
    const params = {};
    return engine.compileAndInit(logicManager,contractJson,params,currentTime,utcOffset);
}

/**
 * Trigger the Ergo contract with a request
 *
 * @param {object} engine - the execution engine
 * @param {object} logicManager - the Template Logic
 * @param {object} contractJson - contract data in JSON
 * @param {object} stateJson - state data in JSON
 * @param {string} currentTime - the definition of 'now'
 * @param {utcOffset} utcOffset - UTC Offset for this execution
 * @param {object} requestJson - state data in JSON
 * @returns {object} Promise to the response
 */
function trigger(engine,logicManager,contractJson,stateJson,currentTime,utcOffset,requestJson) {
    return engine.compileAndTrigger(logicManager,contractJson,requestJson,stateJson,currentTime,utcOffset);
}

Before(function () {
    this.engine = new Engine();
    this.rootdir = Util.resolveRootDir(this.parameters);
    this.currentTime = '1970-01-01T00:00:00Z';
    this.utcOffset = 0;
    this.logicManager = new LogicManager('es6', null);
    this.state = defaultState;
});

Given('the target platform {string}', function (target) {
    this.logicManager.setTarget(target);
});

Given('the current time is {string}', function(currentTime) {
    this.currentTime = currentTime;
});

Given('the UTC offset is {int}', function(utcOffset) {
    this.utcOffset = utcOffset;
});

Given('the Ergo contract {string} in file {string}', function(paramName,paramFile) {
    this.logicManager.setContractName(paramName);
    const fileName = Path.resolve(this.rootdir, paramFile);
    const logicFile = Fs.readFileSync(fileName, 'utf8');
    this.logicManager.addLogicFile(logicFile,paramFile);
});

Given('the Ergo logic in file {string}', function(paramFile) {
    const fileName = Path.resolve(this.rootdir, paramFile);
    const logicFile = Fs.readFileSync(fileName, 'utf8');
    this.logicManager.addLogicFile(logicFile,paramFile);
});

Given('the model in file {string}', function(paramFile) {
    const fileName = Path.resolve(this.rootdir, paramFile);
    const modelFile = Fs.readFileSync(fileName, 'utf8');
    this.logicManager.getModelManager().addAPModelFile(modelFile,paramFile);
});

Given('the contract data', function (actualContract) {
    this.contract = JSON.parse(actualContract);
});

Given('the state', function (actualState) {
    this.state = JSON.parse(actualState);
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
        return Util.compareSuccess({ response },this.answer);
    } else {
        return trigger(this.engine,this.logicManager,this.contract,this.state,this.currentTime,this.utcOffset,this.request)
            .then((actualAnswer) => {
                this.answer = actualAnswer;
                expect(actualAnswer).to.have.property('response');
                expect(actualAnswer).to.not.have.property('error');
                return Util.compareSuccess({ response },actualAnswer);
            });
    }
});

Then('the initial state( of the contract) should be', function (expectedState) {
    const state = JSON.parse(expectedState);
    return init(this.engine,this.logicManager,this.contract,this.currentTime,this.utcOffset)
        .then((actualAnswer) => {
            expect(actualAnswer).to.have.property('state');
            expect(actualAnswer).to.not.have.property('error');
            return Util.compareSuccess({ state },actualAnswer);
        });
});

Then('the initial state( of the contract) should be the default state', function () {
    const state = defaultState;
    return init(this.engine,this.logicManager,this.contract,this.currentTime,this.utcOffset)
        .then((actualAnswer) => {
            expect(actualAnswer).to.have.property('state');
            expect(actualAnswer).to.not.have.property('error');
            return Util.compareSuccess({ state },actualAnswer);
        });
});

Then('the new state( of the contract) should be', function (expectedState) {
    const state = JSON.parse(expectedState);
    if (this.answer) {
        expect(this.answer).to.have.property('state');
        expect(this.answer).to.not.have.property('error');
        return Util.compareSuccess({ state },this.answer);
    } else {
        return trigger(this.engine,this.logicManager,this.contract,this.state,this.currentTime,this.utcOffset,this.request)
            .then((actualAnswer) => {
                this.answer = actualAnswer;
                expect(actualAnswer).to.have.property('state');
                expect(actualAnswer).to.not.have.property('error');
                return Util.compareSuccess({ state },actualAnswer);
            });
    }
});

Then('the following obligations have( also) been emitted', function (expectedEmit) {
    const emit = JSON.parse(expectedEmit);
    if (this.answer) {
        expect(this.answer).to.have.property('emit');
        expect(this.answer).to.not.have.property('error');
        return Util.compareSuccess({ emit },this.answer);
    } else {
        return trigger(this.engine,this.logicManager,this.contract,this.state,this.currentTime,this.utcOffset,this.request)
            .then((actualAnswer) => {
                this.answer = actualAnswer;
                expect(actualAnswer).to.have.property('emit');
                expect(actualAnswer).to.not.have.property('error');
                return Util.compareSuccess({ emit },actualAnswer);
            });
    }
});

Then('the following initial obligations have( also) been emitted', function (expectedEmit) {
    const emit = JSON.parse(expectedEmit);
    return init(this.engine,this.logicManager,this.contract,this.currentTime,this.utcOffset)
        .then((actualAnswer) => {
            this.answer = actualAnswer;
            expect(actualAnswer).to.have.property('emit');
            expect(actualAnswer).to.not.have.property('error');
            return Util.compareSuccess({ emit },actualAnswer);
        });
});

Then('it should fail with the error', function (expectedError) {
    return trigger(this.engine,this.logicManager,this.contract,this.state,this.currentTime,this.utcOffset,this.request)
        .catch((actualError) => {
            expect(actualError.message).to.equal(expectedError);
        });
});

Then('it should fail to initialize with the error', function (expectedError) {
    return init(this.engine,this.logicManager,this.contract,this.currentTime,this.utcOffset)
        .catch((actualError) => {
            expect(actualError.message).to.equal(expectedError);
        });
});
