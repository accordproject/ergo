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
const LogicManager = require('@accordproject/ergo-compiler').LogicManager;
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
 * Load a file or JSON string
 *
 * @param {object} input either a file name or a json string
 * @return {string} content of file
 */
function getTemplate(input) {
    if (!input) {
        return null;
    } else {
        if (input.file) {
            const content = Fs.readFileSync(input.file, 'utf8');
            return { content: content, name: input.file };
        } else {
            return input;
        }
    }
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
     * @param {string} contractInput the contract data
     * @param {string} stateInput the contract state
     * @param {string} currentTime the definition of 'now'
     * @param {string[]} requestsInput the requests
     * @param {string} templateInput the template
     * @param {boolean} warnings whether to print warnings
     * @returns {object} Promise to the result of execution
     */
    static execute(ergoPaths,ctoPaths,contractInput,stateInput,currentTime,requestsInput,templateInput,warnings) {
        try {
            // Get the template if provided
            const sourceTemplate = getTemplate(templateInput);
            const engine = new Engine();
            const logicManager = new LogicManager('es6', sourceTemplate, { warnings });
            logicManager.addErgoBuiltin();
            if (!ergoPaths) { return Promise.reject('No input ergo found'); }
            for (let i = 0; i < ergoPaths.length; i++) {
                const ergoFile = ergoPaths[i];
                const ergoContent = Fs.readFileSync(ergoFile, 'utf8');
                logicManager.addLogicFile(ergoContent, ergoFile);
            }
            if (!ctoPaths) { ctoPaths = []; }
            for (let i = 0; i < ctoPaths.length; i++) {
                const ctoFile = ctoPaths[i];
                const ctoContent = Fs.readFileSync(ctoFile, 'utf8');
                logicManager.addModelFile(ctoContent, ctoFile);
            }
            const contractJson = getJson(contractInput);
            let requestsJson = [];
            for (let i = 0; i < requestsInput.length; i++) {
                requestsJson.push(getJson(requestsInput[i]));
            }
            let initResponse;
            if (stateInput === null) {
                initResponse = engine.compileAndInit(logicManager, contractJson, {}, currentTime, null);
            } else {
                const stateJson = getJson(stateInput);
                initResponse = Promise.resolve({ state: stateJson });
            }
            // Get all the other requests and chain execution through Promise.reduce()
            return requestsJson.reduce((promise,requestJson) => {
                return promise.then((result) => {
                    return engine.compileAndExecute(logicManager, contractJson, requestJson, result.state, currentTime, null);
                });
            }, initResponse);
        } catch (err) {
            return Promise.reject(err);
        }
    }

    /**
     * Invoke an Ergo contract's clause
     *
     * @param {string[]} ergoPaths paths to the Ergo modules
     * @param {string[]} ctoPaths paths to CTO models
     * @param {string} clauseName the name of the clause to invoke
     * @param {string} contractInput the contract data
     * @param {string} stateInput the contract state
     * @param {string} currentTime the definition of 'now'
     * @param {object} paramsInput the parameters for the clause
     * @param {string} templateInput the template
     * @param {boolean} warnings whether to print warnings
     * @returns {object} Promise to the result of invocation
     */
    static invoke(ergoPaths,ctoPaths,clauseName,contractInput,stateInput,currentTime,paramsInput,templateInput,warnings) {
        try {
        // Get the template if provided
            const sourceTemplate = getTemplate(templateInput);
            const engine = new Engine();
            const logicManager = new LogicManager('es6', sourceTemplate, { warnings });
            logicManager.addErgoBuiltin();
            if (!ergoPaths) { return Promise.reject('No input ergo found'); }
            for (let i = 0; i < ergoPaths.length; i++) {
                const ergoFile = ergoPaths[i];
                const ergoContent = Fs.readFileSync(ergoFile, 'utf8');
                logicManager.addLogicFile(ergoContent, ergoFile);
            }
            if (!ctoPaths) { ctoPaths = []; }
            for (let i = 0; i < ctoPaths.length; i++) {
                const ctoFile = ctoPaths[i];
                const ctoContent = Fs.readFileSync(ctoFile, 'utf8');
                logicManager.addModelFile(ctoContent, ctoFile);
            }
            const contractJson = getJson(contractInput);
            const clauseParams = getJson(paramsInput);
            const stateJson = getJson(stateInput);
            return engine.compileAndInvoke(logicManager, clauseName, contractJson, clauseParams, stateJson, currentTime, null);
        } catch (err) {
            return Promise.reject(err);
        }
    }

    /**
     * Invoke init for an Ergo contract
     *
     * @param {string[]} ergoPaths paths to the Ergo modules
     * @param {string[]} ctoPaths paths to CTO models
     * @param {string} contractInput the contract data
     * @param {string} currentTime the definition of 'now'
     * @param {object} paramsInput the parameters for the clause
     * @param {string} templateInput the template
     * @param {boolean} warnings whether to print warnings
     * @returns {object} Promise to the result of execution
     */
    static init(ergoPaths,ctoPaths,contractInput,currentTime,paramsInput,templateInput,warnings) {
        try {
            // Get the template if provided
            const sourceTemplate = getTemplate(templateInput);
            const engine = new Engine();
            const logicManager = new LogicManager('es6', sourceTemplate, { warnings });
            logicManager.addErgoBuiltin();
            if (!ergoPaths) { return Promise.reject('No input ergo found'); }
            for (let i = 0; i < ergoPaths.length; i++) {
                const ergoFile = ergoPaths[i];
                const ergoContent = Fs.readFileSync(ergoFile, 'utf8');
                logicManager.addLogicFile(ergoContent, ergoFile);
            }
            if (!ctoPaths) { ctoPaths = []; }
            for (let i = 0; i < ctoPaths.length; i++) {
                const ctoFile = ctoPaths[i];
                const ctoContent = Fs.readFileSync(ctoFile, 'utf8');
                logicManager.addModelFile(ctoContent, ctoFile);
            }
            const contractJson = getJson(contractInput);
            const clauseParams = getJson(paramsInput);
            return engine.compileAndInit(logicManager, contractJson, clauseParams, currentTime, null);
        } catch (err) {
            return Promise.reject(err);
        }
    }

    /**
     * Invoke generateText for an Ergo contract
     *
     * @param {string[]} ergoPaths paths to the Ergo modules
     * @param {string[]} ctoPaths paths to CTO models
     * @param {string} contractInput the contract data
     * @param {string} currentTime the definition of 'now'
     * @param {string} templateInput the template
     * @param {object} options to the text generation
     * @returns {object} Promise to the result of execution
     */
    static generateText(ergoPaths,ctoPaths,contractInput,currentTime,templateInput, options) {
        // Get the template if provided
        const sourceTemplate = getTemplate(templateInput);
        const engine = new Engine();
        const logicManager = new LogicManager('es6',sourceTemplate);
        logicManager.addErgoBuiltin();
        if (!ergoPaths) { return Promise.reject('No input ergo found'); }
        for (let i = 0; i < ergoPaths.length; i++) {
            const ergoFile = ergoPaths[i];
            const ergoContent = Fs.readFileSync(ergoFile, 'utf8');
            logicManager.addLogicFile(ergoContent, ergoFile);
        }
        if (!ctoPaths) { ctoPaths = []; }
        for (let i = 0; i < ctoPaths.length; i++) {
            const ctoFile = ctoPaths[i];
            const ctoContent = Fs.readFileSync(ctoFile, 'utf8');
            logicManager.addModelFile(ctoContent, ctoFile);
        }
        const contractJson = getJson(contractInput);
        const markdownOtions = {
            '$class': 'org.accordproject.ergo.options.Options',
            'wrapVariables': options && options.wrapVariables ? options.wrapVariables : false,
            'template': true,
        };
        return engine.compileAndGenerateText(logicManager,contractJson,{},currentTime,markdownOtions);
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
