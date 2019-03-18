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

const ErgoCompiler = require('@accordproject/ergo-compiler').Compiler;
const Logger = require('@accordproject/ergo-compiler').Logger;
const Util = require('./util');

const Moment = require('moment-mini');
// Make sure Moment serialization preserves utcOffset. See https://momentjs.com/docs/#/displaying/as-json/
Moment.fn.toJSON = Util.momentToJson;

const {
    VM
} = require('vm2');

/**
 * <p>
 * EngineUtil class. Execution of Ergo logic (JavaScript target).
 * </p>
 * @class
 * @public
 * @memberof module:ergo-engine
 */
class EngineUtil {
    /**
     * Execute Ergo contract with request
     *
     * @param {string} ergoCode JavaScript code for ergo logic
     * @param {string} codeKind either 'es6' or 'es5'
     * @param {string} contractName of the contract to execute
     * @param {object} contractJson the contract data in JSON
     * @param {object} stateJson the state in JSON
     * @param {string} currentTime the definition of 'now'
     * @param {object} requestJson the request transaction in JSON
     * @returns {object} Promise to the result of execution
     */
    static executeRequestToContract(ergoCode,codeKind,contractName,contractJson,stateJson,currentTime,requestJson) {
        const now = Util.setCurrentTime(currentTime);
        const vm = new VM({
            timeout: 1000,
            sandbox: {
                moment: Moment,
                logger: Logger,
                utcOffset: now.utcOffset()
            }
        });

        // add immutables to the context
        const params = { 'contract': contractJson, 'request': requestJson, 'state': stateJson, 'emit': [], 'now': now };
        vm.freeze(params, 'params'); // Add the context
        vm.run(ergoCode); // Load the generated logic
        let contract;
        let clauseCall;
        if (codeKind === 'es5') {
            contract = '';
            clauseCall = 'main(params);'; // Create the clause call
        } else {
            contract = 'let contract = new ' + ErgoCompiler.contractCallName(contractName) + '();'; // Instantiate the contract
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
     * @param {string} contractName of the contract
     * @param {string} clauseName of the contract to invoke
     * @param {object} contractJson the contract data in JSON
     * @param {object} stateJson the state in JSON
     * @param {string} currentTime the definition of 'now'
     * @param {object} clauseParams the clause parameters
     * @returns {object} Promise to the result of invocation
     */
    static invokeContractClause(ergoCode,codeKind,contractName,clauseName,contractJson,stateJson,currentTime,clauseParams) {
        const now = Util.setCurrentTime(currentTime);
        const vm = new VM({
            timeout: 1000,
            sandbox: {
                moment: Moment,
                logger: Logger,
                utcOffset: now.utcOffset()
            }
        });

        // add immutables to the context
        const params = Object.assign({}, { 'contract': contractJson, 'state': stateJson, 'emit': [], 'now': now }, clauseParams);
        vm.freeze(params, 'params'); // Add the context
        vm.run(ergoCode); // Load the generated logic
        let contract;
        let clauseCall;
        if (codeKind === 'es5') {
            contract = '';
            clauseCall = clauseName+'(params);'; // Create the clause call
        } else {
            contract = 'let contract = new ' + ErgoCompiler.contractCallName(contractName) + '();'; // Instantiate the contract
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
     * @param {string} contractName of the contract
     * @param {object} contractJson the contract data in JSON
     * @param {string} currentTime the definition of 'now'
     * @param {object} clauseParams the clause parameters
     * @returns {object} Promise to the result of execution
     */
    static invokeInit(ergoCode,codeKind,contractName,contractJson,currentTime,clauseParams) {
        const defaultState = {'stateId':'org.accordproject.cicero.contract.AccordContractState#1','$class':'org.accordproject.cicero.contract.AccordContractState'};
        return this.invokeContractClause(ergoCode,codeKind,contractName,'init',contractJson,defaultState,currentTime,clauseParams);
    }

    /**
     * Compile, then execute the Contract with a request
     *
     * @param {Array<{name:string, content:string}>} ergoSources Ergo modules
     * @param {Array<{name:string, content:string}>} ctoSources CTO models
     * @param {string} codeKind either 'es6' or 'es5'
     * @param {string} contractName of the contract
     * @param {object} contractJson the contract data in JSON
     * @param {object} stateJson the state in JSON
     * @param {string} currentTime the definition of 'now'
     * @param {object} requestJson the request transaction in JSON
     * @returns {object} Promise to the result of execution
     */
    static execute(ergoSources,ctoSources,codeKind,contractName,contractJson,stateJson,currentTime,requestJson) {
        return (ErgoCompiler.compile(ergoSources,ctoSources,codeKind,true)).then((ergoCode) => {
            if (ergoCode.hasOwnProperty('error')) {
                return ergoCode;
            } else {
                return this.executeRequestToContract(ergoCode.success,codeKind,contractName,contractJson,stateJson,currentTime,requestJson);
            }
        });
    }

    /**
     * Compile then invoke a clause of the contract
     *
     * @param {Array<{name:string, content:string}>} ergoSources Ergo modules
     * @param {Array<{name:string, content:string}>} ctoSources CTO models
     * @param {string} codeKind either 'es6' or 'es5'
     * @param {string} contractName of the contract
     * @param {string} clauseName of the contract to invoke
     * @param {object} contractJson the contract data in JSON
     * @param {object} stateJson the state in JSON
     * @param {string} currentTime the definition of 'now'
     * @param {object} clauseParams the clause parameters
     * @returns {object} Promise to the result of invocation
     */
    static invoke(ergoSources,ctoSources,codeKind,contractName,clauseName,contractJson,stateJson,currentTime,clauseParams) {
        return (ErgoCompiler.compile(ergoSources,ctoSources,codeKind,true)).then((ergoCode) => {
            if (ergoCode.hasOwnProperty('error')) {
                return ergoCode;
            } else {
                return this.invokeContractClause(ergoCode.success,codeKind,contractName,clauseName,contractJson,stateJson,currentTime,clauseParams);
            }
        });
    }

    /**
     * Compile then invoke the init clause of the contract
     *
     * @param {Array<{name:string, content:string}>} ergoSources Ergo modules
     * @param {Array<{name:string, content:string}>} ctoSources CTO models
     * @param {string} codeKind either 'es6' or 'es5'
     * @param {string} contractName of the contract
     * @param {object} contractJson the contract data in JSON
     * @param {string} currentTime the definition of 'now'
     * @param {object} clauseParams the clause parameters
     * @returns {object} Promise to the result of invocation
     */
    static init(ergoSources,ctoSources,codeKind,contractName,contractJson,currentTime,clauseParams) {
        return (ErgoCompiler.compile(ergoSources,ctoSources,codeKind,true)).then((ergoCode) => {
            if (ergoCode.hasOwnProperty('error')) {
                return ergoCode;
            } else {
                return this.invokeInit(ergoCode.success,codeKind,contractName,contractJson,currentTime,clauseParams);
            }
        });
    }
}

module.exports = EngineUtil;
