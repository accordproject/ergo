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
const ErgoCompiler = require('@accordproject/ergo-compiler').Compiler;
const TemplateLogic = require('@accordproject/ergo-compiler').TemplateLogic;
const Engine = require('@accordproject/ergo-engine').VMEngine;

/**
 * Load a file or JSON string
 *
 * @param {object} input either a file name or a json string
 * @return {object} JSON object
 */
function getJson(input) {
    let jsonString;
    if (input.file) {
        jsonString = Fs.readFileSync(input.file, 'utf8');
    } else {
        jsonString = input.content;
    }
    return JSON.parse(jsonString);
}

/**
 * Utility class that implements the commands exposed by the Ergo CLI.
 * @class
 */
class Commands {
    /**
     * Execute an Ergo contract with a request
     *
     * @param {string[]} ergoPaths paths to the Ergo modules
     * @param {string[]} ctoPaths paths to CTO models
     * @param {string} contractName of the contract
     * @param {string} contractInput the contract data
     * @param {string} stateInput the contract state
     * @param {string} currentTime the definition of 'now'
     * @param {string[]} requestsInput the requests
     * @returns {object} Promise to the result of execution
     */
    static execute(ergoPaths,ctoPaths,contractName,contractInput,stateInput,currentTime,requestsInput) {
        const engine = new Engine();
        const templateLogic = new TemplateLogic('es6');
        templateLogic.addErgoBuiltin();
        templateLogic.setContractName(contractName);
        if (!ergoPaths) { return Promise.reject('No input ergo found'); }
        for (let i = 0; i < ergoPaths.length; i++) {
            const ergoFile = ergoPaths[i];
            const ergoContent = Fs.readFileSync(ergoFile, 'utf8');
            templateLogic.addLogicFile(ergoContent, ergoFile);
        }
        if (!ctoPaths) { ctoPaths = []; }
        for (let i = 0; i < ctoPaths.length; i++) {
            const ctoFile = ctoPaths[i];
            const ctoContent = Fs.readFileSync(ctoFile, 'utf8');
            templateLogic.addModelFile(ctoContent, ctoFile);
        }
        const contractJson = getJson(contractInput);
        let requestsJson = [];
        for (let i = 0; i < requestsInput.length; i++) {
            requestsJson.push(getJson(requestsInput[i]));
        }
        let initResponse;
        if (stateInput === null) {
            initResponse = engine.compileAndInit(templateLogic, contractName, contractJson, {}, currentTime);
        } else {
            const stateJson = getJson(stateInput);
            initResponse = Promise.resolve({ state: stateJson });
        }
        // Get all the other requests and chain execution through Promise.reduce()
        return requestsJson.reduce((promise,requestJson) => {
            return promise.then((result) => {
                return engine.compileAndExecute(templateLogic,contractName,contractJson,requestJson,result.state,currentTime);
            });
        }, initResponse);
    }

    /**
     * Invoke an Ergo contract's clause
     *
     * @param {string[]} ergoPaths paths to the Ergo modules
     * @param {string[]} ctoPaths paths to CTO models
     * @param {string} contractName the contract
     * @param {string} clauseName the name of the clause to invoke
     * @param {string} contractInput the contract data
     * @param {string} stateInput the contract state
     * @param {string} currentTime the definition of 'now'
     * @param {object} paramsInput the parameters for the clause
     * @returns {object} Promise to the result of invocation
     */
    static invoke(ergoPaths,ctoPaths,contractName,clauseName,contractInput,stateInput,currentTime,paramsInput) {
        const engine = new Engine();
        const templateLogic = new TemplateLogic('es6');
        templateLogic.addErgoBuiltin();
        templateLogic.setContractName(contractName);
        if (!ergoPaths) { return Promise.reject('No input ergo found'); }
        for (let i = 0; i < ergoPaths.length; i++) {
            const ergoFile = ergoPaths[i];
            const ergoContent = Fs.readFileSync(ergoFile, 'utf8');
            templateLogic.addLogicFile(ergoContent, ergoFile);
        }
        if (!ctoPaths) { ctoPaths = []; }
        for (let i = 0; i < ctoPaths.length; i++) {
            const ctoFile = ctoPaths[i];
            const ctoContent = Fs.readFileSync(ctoFile, 'utf8');
            templateLogic.addModelFile(ctoContent, ctoFile);
        }
        const contractJson = getJson(contractInput);
        const clauseParams = getJson(paramsInput);
        const stateJson = getJson(stateInput);
        return engine.compileAndInvoke(templateLogic,contractName,clauseName,contractJson,clauseParams,stateJson,currentTime);
    }

    /**
     * Invoke init for an Ergo contract
     *
     * @param {string[]} ergoPaths paths to the Ergo modules
     * @param {string[]} ctoPaths paths to CTO models
     * @param {string} contractName the contract name
     * @param {string} contractInput the contract data
     * @param {string} currentTime the definition of 'now'
     * @param {object} paramsInput the parameters for the clause
     * @returns {object} Promise to the result of execution
     */
    static init(ergoPaths,ctoPaths,contractName,contractInput,currentTime,paramsInput) {
        const engine = new Engine();
        const templateLogic = new TemplateLogic('es6');
        templateLogic.addErgoBuiltin();
        templateLogic.setContractName(contractName);
        if (!ergoPaths) { return Promise.reject('No input ergo found'); }
        for (let i = 0; i < ergoPaths.length; i++) {
            const ergoFile = ergoPaths[i];
            const ergoContent = Fs.readFileSync(ergoFile, 'utf8');
            templateLogic.addLogicFile(ergoContent, ergoFile);
        }
        if (!ctoPaths) { ctoPaths = []; }
        for (let i = 0; i < ctoPaths.length; i++) {
            const ctoFile = ctoPaths[i];
            const ctoContent = Fs.readFileSync(ctoFile, 'utf8');
            templateLogic.addModelFile(ctoContent, ctoFile);
        }
        const contractJson = getJson(contractInput);
        const clauseParams = getJson(paramsInput);
        return engine.compileAndInit(templateLogic,contractName,contractJson,clauseParams,currentTime);
    }

    /**
     * Parse CTO to JSON File
     *
     * @param {string} ctoPath path to CTO model file
     * @returns {string} The name of the generated CTOJ model file
     */
    static parseCTOtoFileSync(ctoPath) {
        const ctoSource = Fs.readFileSync(ctoPath, 'utf8');
        const result = ErgoCompiler.parseCTOtoJSON(ctoSource);
        const outFile = ctoPath.substr(0, ctoPath.lastIndexOf('.')) + '.ctoj';
        Fs.writeFileSync(outFile, JSON.stringify(result));
        return outFile;
    }

    /**
     * Parse CTO to JSON File
     *
     * @param {string} ctoPath path to CTO model file
     * @returns {string} The name of the generated CTOJ model file
     */
    static parseCTOtoFile(ctoPath) {
        return Promise.resolve(this.parseCTOtoFileSync(ctoPath));
    }
}

module.exports = Commands;
