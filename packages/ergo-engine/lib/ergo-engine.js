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
// Make sure Moment serialization preserves utcOffset. See https://momentjs.com/docs/#/displaying/as-json/
Moment.fn.toJSON = require('./momentToJson');
const Logger = require('@accordproject/ergo-compiler/lib/logger');

const {
    VM
} = require('vm2');

const defaultState = {'stateId':'org.accordproject.cicero.contract.AccordContractState#1','$class':'org.accordproject.cicero.contract.AccordContractState'};

/**
 * Utility class that implements the internals for Ergo.
 * @class
 */
class ErgoEngine {
    /**
     * Ensures there is a proper current time
     *
     * @param {string} currentTime the definition of 'now'
     * @returns {object} if valid, the moment object for the current time
     */
    static initCurrentTime(currentTime) {
        if (!currentTime) {
            throw new Error('Calls to Ergo engine should provide a current time');
        }
        const now = Moment.parseZone(currentTime, 'YYYY-MM-DDTHH:mm:ssZ', true);
        if (now.isValid()) {
            return now;
        } else {
            throw new Error(`${currentTime} is not a valid moment in format 'YYYY-MM-DDTHH:mm:ssZ'`);
        }
    }

    /**
     * Send request to Ergo contract
     *
     * @param {string} ergoCode JavaScript code for ergo logic
     * @param {string} codeKind either 'es6' or 'es5'
     * @param {object} contractJson the contract data in JSON
     * @param {object} requestJson the request transaction in JSON
     * @param {object} stateJson the state in JSON
     * @param {string} contractName of the contract to execute
     * @param {string} currentTime the definition of 'now'
     * @returns {object} Promise to the result of execution
     */
    static sendRequestToContract(ergoCode,codeKind,contractJson,requestJson,stateJson,contractName,currentTime) {
        const now = this.initCurrentTime(currentTime);
        const vm = new VM({
            timeout: 1000,
            sandbox: {
                moment: Moment,
                logger: Logger,
                utcOffset: now.utcOffset()
            }
        });

        // add immutables to the context
        const params = { 'contract': contractJson, 'request': requestJson, 'state': stateJson, 'emit': [], 'now': now, 'utcOffset': now.utcOffset };
        vm.freeze(params, 'params'); // Add the context
        vm.run(ergoCode); // Load the generated logic
        let contract;
        let clauseCall;
        if (codeKind === 'es5') {
            contract = '';
            clauseCall = 'main(params);'; // Create the clause call
        } else {
            contract = 'let contract = new ' + Ergo.contractCallName(contractName) + '();'; // Instantiate the contract
            clauseCall = 'contract.main(params);'; // Create the clause call
        }
        const result = vm.run(contract + clauseCall); // Call the logic
        if (result.hasOwnProperty('left')) {
            return Promise.resolve(result.left);
        } else {
            return Promise.resolve({ 'error' : { 'kind' : 'ErgoError', 'message' : result.right } });
        }
    }

    /**
     * Invoke a clause of the contract
     *
     * @param {string} ergoCode JavaScript code for ergo logic
     * @param {string} codeKind either 'es6' or 'es5'
     * @param {object} contractJson the contract data in JSON
     * @param {object} clauseParams the clause parametters
     * @param {object} stateJson the state in JSON
     * @param {string} contractName of the contract to execute
     * @param {string} clauseName of the contract to execute
     * @param {string} currentTime the definition of 'now'
     * @returns {object} Promise to the result of execution
     */
    static invokeContractClause(ergoCode,codeKind,contractJson,clauseParams,stateJson,contractName,clauseName,currentTime) {
        const now = this.initCurrentTime(currentTime);
        const vm = new VM({
            timeout: 1000,
            sandbox: {
                moment: Moment,
                logger: Logger,
                utcOffset: now.utcOffset()
            }
        });

        // add immutables to the context
        const params = Object.assign({}, { 'contract': contractJson, 'state': stateJson, 'emit': [], 'now': now, 'utcOffset': now.utcOffset }, clauseParams);
        vm.freeze(params, 'params'); // Add the context
        vm.run(ergoCode); // Load the generated logic
        let contract;
        let clauseCall;
        if (codeKind === 'es5') {
            contract = '';
            clauseCall = clauseName+'(params);'; // Create the clause call
        } else {
            contract = 'let contract = new ' + Ergo.contractCallName(contractName) + '();'; // Instantiate the contract
            clauseCall = 'contract.' + clauseName+ '(params);'; // Create the clause call
        }
        const result = vm.run(contract + clauseCall); // Call the logic
        if (result.hasOwnProperty('left')) {
            return Promise.resolve(result.left);
        } else {
            return Promise.resolve({ 'error' : { 'kind' : 'ErgoError', 'message' : result.right } });
        }
    }

    /**
     * Invoke the init clause of the contract
     *
     * @param {string} ergoCode JavaScript code for ergo logic
     * @param {string} codeKind either 'es6' or 'es5'
     * @param {object} contractJson the contract data in JSON
     * @param {object} clauseParams the clause parametters
     * @param {string} contractName of the contract to execute
     * @param {string} currentTime the definition of 'now'
     * @returns {object} Promise to the result of execution
     */
    static invokeInit(ergoCode,codeKind,contractJson,clauseParams,contractName,currentTime) {
        return this.invokeContractClause(ergoCode,codeKind,contractJson,clauseParams,defaultState,contractName,'init',currentTime);
    }

    /**
     * Compile, then send Request to Contract
     *
     * @param {Array<{name:string, content:string}>} ergoSources Ergo modules
     * @param {Array<{name:string, content:string}>} ctoSources CTO models
     * @param {string} codeKind either 'es6' or 'es5'
     * @param {object} contractJson the contract data in JSON
     * @param {object} requestJson the request transaction in JSON
     * @param {object} stateJson the state in JSON
     * @param {string} contractName of the contract to send
     * @param {string} currentTime the definition of 'now'
     * @returns {object} Promise to the result of execution
     */
    static send(ergoSources,ctoSources,codeKind,contractJson,requestJson,stateJson,contractName,currentTime) {
        return (Ergo.compile(ergoSources,ctoSources,codeKind,true)).then((ergoCode) => {
            if (ergoCode.hasOwnProperty('error')) {
                return ergoCode;
            } else {
                return this.sendRequestToContract(ergoCode.success,codeKind,contractJson,requestJson,stateJson,contractName,currentTime);
            }
        });
    }

    /**
     * Compile then invoke a clause of the contract
     *
     * @param {Array<{name:string, content:string}>} ergoSources Ergo modules
     * @param {Array<{name:string, content:string}>} ctoSources CTO models
     * @param {string} codeKind either 'es6' or 'es5'
     * @param {object} contractJson the contract data in JSON
     * @param {object} clauseParams the clause parametters
     * @param {object} stateJson the state in JSON
     * @param {string} contractName of the contract to execute
     * @param {string} clauseName of the contract to execute
     * @param {string} currentTime the definition of 'now'
     * @returns {object} Promise to the result of execution
     */
    static invoke(ergoSources,ctoSources,codeKind,contractJson,clauseParams,stateJson,contractName,clauseName,currentTime) {
        return (Ergo.compile(ergoSources,ctoSources,codeKind,true)).then((ergoCode) => {
            if (ergoCode.hasOwnProperty('error')) {
                return ergoCode;
            } else {
                return this.invokeContractClause(ergoCode.success,codeKind,contractJson,clauseParams,stateJson,contractName,clauseName,currentTime);
            }
        });
    }

    /**
     * Compile then invoke the init clause of the contract
     *
     * @param {Array<{name:string, content:string}>} ergoSources Ergo modules
     * @param {Array<{name:string, content:string}>} ctoSources CTO models
     * @param {string} codeKind either 'es6' or 'es5'
     * @param {object} contractJson the contract data in JSON
     * @param {object} clauseParams the clause parametters
     * @param {string} contractName of the contract to execute
     * @param {string} currentTime the definition of 'now'
     * @returns {object} Promise to the result of execution
     */
    static init(ergoSources,ctoSources,codeKind,contractJson,clauseParams,contractName,currentTime) {
        return (Ergo.compile(ergoSources,ctoSources,codeKind,true)).then((ergoCode) => {
            if (ergoCode.hasOwnProperty('error')) {
                return ergoCode;
            } else {
                return this.invokeInit(ergoCode.success,codeKind,contractJson,clauseParams,contractName,currentTime);
            }
        });
    }
}

module.exports = ErgoEngine;
