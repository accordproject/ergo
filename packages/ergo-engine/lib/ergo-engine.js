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

const Ergo=require('@accordproject/ergo-compiler/lib/ergo');
const Moment = require('moment');
const Logger = require('@accordproject/ergo-compiler/lib/logger');

const {
    VM
} = require('vm2');

/**
 * Utility class that implements the internals for Ergo.
 * @class
 */
class ErgoEngine {
    /**
     * Execute compiled Ergo code
     *
     * @param {string} ergoCode JavaScript code for ergo logic
     * @param {object} contractJson the contract data in JSON
     * @param {object} requestJson the request transaction in JSON
     * @param {object} stateJson the state in JSON
     * @param {string} contractName of the contract to execute
     * @returns {object} Promise to the result of execution
     */
    static executeErgoCode(ergoCode,contractJson,requestJson,stateJson,contractName) {
        const vm = new VM({
            timeout: 1000,
            sandbox: {
                moment: Moment,
                logger: Logger
            }
        });

        // add immutables to the context
        const params = { 'contract': contractJson, 'request': requestJson, 'state': stateJson, 'emit': [], 'now': Moment() };
        vm.freeze(params, 'params'); // Add the context
        vm.run(ergoCode); // Load the generated logic
        const contract = 'let contract = new ' + Ergo.contractCallName(contractName) + '();'; // Instantiate the contract
        const clauseCall = 'contract.main(params);'; // Create the clause call
        const result = vm.run(contract + clauseCall); // Call the logic
        if (result.hasOwnProperty('left')) {
            return Promise.resolve(result.left);
        } else {
            return Promise.resolve({ 'error' : { 'kind' : 'ErgoError', 'message' : result.right } });
        }
    }

    /**
     * Initialize state
     *
     * @param {string} ergoCode JavaScript code for ergo logic
     * @param {object} contractJson the contract data in JSON
     * @param {object} requestJson the request transaction in JSON
     * @param {string} contractName of the contract to initialize
     * @returns {object} Promise to the result of initialization
     */
    static initErgoCode(ergoCode,contractJson,requestJson,contractName) {
        const vm = new VM({
            timeout: 1000,
            sandbox: {
                moment: Moment,
                logger: Logger
            }
        });

        // add immutables to the context
        const params = { 'contract': contractJson, 'request': requestJson, 'state': {}, 'emit': [], 'now': Moment() };
        vm.freeze(params, 'params'); // Add the context
        vm.run(ergoCode); // Load the generated logic
        const contract = 'let contract = new ' + Ergo.contractCallName(contractName) + '();'; // Instantiate the contract
        const clauseCall = 'contract.init(params);'; // Create the clause call
        const result = vm.run(contract + clauseCall); // Call the logic
        if (result.hasOwnProperty('left')) {
            return Promise.resolve(result.left);
        } else {
            return Promise.resolve({ 'error' : { 'kind' : 'ErgoError', 'message' : result.right } });
        }
    }

    /**
     * Execute Ergo (JavaScript)
     *
     * @param {Array<{name:string, content:string}>} ergoSources Ergo modules
     * @param {Array<{name:string, content:string}>} ctoSources CTO models
     * @param {object} contractJson the contract data in JSON
     * @param {object} requestJson the request transaction in JSON
     * @param {object} stateJson the state in JSON
     * @param {string} contractName of the contract to execute
     * @returns {object} Promise to the result of execution
     */
    static execute(ergoSources,ctoSources,contractJson,requestJson,stateJson,contractName) {
        return (Ergo.compileAndLink(ergoSources,ctoSources,'javascript')).then((ergoCode) => {
            if (ergoCode.hasOwnProperty('error')) {
                return ergoCode;
            } else {
                return this.executeErgoCode(ergoCode.success,contractJson,requestJson,stateJson,contractName);
            }
        });
    }

    /**
     * Initialize Ergo contract state (JavaScript)
     *
     * @param {Array<{name:string, content:string}>} ergoSources Ergo modules
     * @param {Array<{name:string, content:string}>} ctoSources CTO models
     * @param {object} contractJson the contract data in JSON
     * @param {object} requestJson the request transaction in JSON
     * @param {string} contractName of the contract to execute
     * @returns {object} Promise to the result of execution
     */
    static init(ergoSources,ctoSources,contractJson,requestJson,contractName) {
        return (Ergo.compileAndLink(ergoSources,ctoSources,'javascript')).then((ergoCode) => {
            if (ergoCode.hasOwnProperty('error')) {
                return ergoCode;
            } else {
                return this.initErgoCode(ergoCode.success,contractJson,requestJson,contractName);
            }
        });
    }

}

module.exports = ErgoEngine;
