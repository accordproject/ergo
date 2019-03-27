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

const Logger = require('@accordproject/ergo-compiler').Logger;
const Util = require('./util');

const Moment = require('moment-mini');
// Make sure Moment serialization preserves utcOffset. See https://momentjs.com/docs/#/displaying/as-json/
Moment.fn.toJSON = Util.momentToJson;

const {
    VM,
    VMScript
} = require('vm2');

/**
 * <p>
 * Engine class. Execution of template logic against a request object, returning a response to the caller.
 * </p>
 * @class
 * @public
 * @memberof module:ergo-engine
 */
class Engine {

    /**
     * Create the Engine.
     */
    constructor() {
        this.scripts = {};
    }

    /**
     * Compile and cache JavaScript logic
     * @param {ScriptManager} scriptManager  - the script manager
     * @param {string} contractId - the contract identifier
     * @return {VMScript} the cached script
     * @private
     */
    cacheJsScript(scriptManager, contractId) {
        if (!this.scripts[contractId]) {
            const allJsScripts = scriptManager.getCompiledJavaScript();
            const script = new VMScript(allJsScripts);
            this.scripts[contractId] = script;
        }
        return this.scripts[contractId];
    }

    /**
     * Execute a clause, passing in the request object
     * @param {TemplateLogic} logic  - the logic to execute
     * @param {string} contractId - the contract identifier
     * @param {object} contract - the contract data
     * @param {object} request - the request, a JS object that can be deserialized
     * using the Composer serializer.
     * @param {object} state - the contract state, a JS object that can be deserialized
     * using the Composer serializer.
     * @param {string} currentTime - the definition of 'now'
     * @return {Promise} a promise that resolves to a result for the clause
     */
    async execute(logic, contractId, contract, request, state, currentTime) {
        // Set the current time and UTC Offset
        const now = Util.setCurrentTime(currentTime);
        const utcOffset = now.utcOffset();

        const validContract = logic.validateInput(contract); // ensure the contract is valid
        const validRequest = logic.validateInput(request); // ensure the request is valid
        const validState = logic.validateInput(state); // ensure the state is valid

        Logger.debug('Engine processing request ' + request.$class + ' with state ' + state.$class);

        const script = this.cacheJsScript(logic.getScriptManager(), contractId);
        const callScript = logic.getDispatchCall();

        const vm = new VM({
            timeout: 1000,
            sandbox: {
                moment: Moment,
                logger: Logger,
                utcOffset: utcOffset
            }
        });

        // add immutables to the context
        vm.freeze(validContract, 'data');
        vm.freeze(validState, 'state');
        vm.freeze(now, 'now');
        vm.freeze(validRequest, 'request');

        // execute the logic
        vm.run(script);
        const result = vm.run(callScript);

        const validResponse = logic.validateOutput(result.response); // ensure the response is valid
        const validNewState = logic.validateOutput(result.state); // ensure the new state is valid
        const validEmit = logic.validateOutputArray(result.emit); // ensure all the emits are valid

        return {
            'clause': contractId,
            'request': validRequest,
            'response': validResponse,
            'state': validNewState,
            'emit': validEmit,
        };
    }

    /**
     * Invoke a clause, passing in the parameters for that clause
     * @param {TemplateLogic} logic  - the logic to execute
     * @param {string} contractId - the contract identifier
     * @param {string} clauseName - the clause name
     * @param {object} contract - the contract data
     * @param {object} params - the clause parameters
     * @param {object} state - the contract state, a JS object that can be deserialized
     * using the Composer serializer.
     * @param {string} currentTime - the definition of 'now'
     * @return {Promise} a promise that resolves to a result for the clause
     */
    async invoke(logic, contractId, clauseName, contract, params, state, currentTime) {
        // Set the current time and UTC Offset
        const now = Util.setCurrentTime(currentTime);
        const utcOffset = now.utcOffset();

        const validContract = logic.validateInput(contract); // ensure the contract is valid
        const validParams = logic.validateInputRecord(params); // ensure the parameters are valid
        const validState = logic.validateInput(state); // ensure the state is valid

        Logger.debug('Engine processing clause ' + clauseName + ' with state ' + state.$class);

        const script = this.cacheJsScript(logic.getScriptManager(), contractId);
        const callScript = logic.getInvokeCall(clauseName);

        const vm = new VM({
            timeout: 1000,
            sandbox: {
                moment: Moment,
                logger: Logger,
                utcOffset: utcOffset
            }
        });

        // add immutables to the context
        vm.freeze(validContract, 'data');
        vm.freeze(validState, 'state');
        vm.freeze(now, 'now');
        vm.freeze(validParams, 'params');

        // execute the logic
        vm.run(script);
        const result = vm.run(callScript);

        const validResponse = logic.validateOutput(result.response); // ensure the response is valid
        const validNewState = logic.validateOutput(result.state); // ensure the new state is valid
        const validEmit = logic.validateOutputArray(result.emit); // ensure all the emits are valid

        return {
            'clause': contractId,
            'params': validParams,
            'response': validResponse,
            'state': validNewState,
            'emit': validEmit,
        };
    }

    /**
     * Initialize a clause
     * @param {TemplateLogic} logic  - the logic to execute
     * @param {string} contractId - the contract identifier
     * @param {object} contract - the contract data
     * @param {object} params - the clause parameters
     * @param {string} currentTime - the definition of 'now'
     * @return {Promise} a promise that resolves to a result for the clause initialization
     */
    async init(logic, contractId, contract, params, currentTime) {
        const defaultState = {
            '$class':'org.accordproject.cicero.contract.AccordContractState',
            'stateId':'org.accordproject.cicero.contract.AccordContractState#1'
        };
        return this.invoke(logic, contractId, 'init', contract, params, defaultState, currentTime);
    }

    /**
     * Compile then initialize a clause
     *
     * @param {TemplateLogic} logic  - the logic to execute
     * @param {string} contractId - the contract identifier
     * @param {object} contract - the contract data
     * @param {object} params - the clause parameters
     * @param {string} currentTime - the definition of 'now'
     * @return {Promise} a promise that resolves to a result for the clause initialization
     */
    compileAndInit(logic, contractId, contract, params, currentTime) {
        return logic.compileLogic(false).then(() => {
            return this.init(logic, contractId, contract, params, currentTime);
        });
    }

    /**
     * Compile then invoke a clause
     *
     * @param {TemplateLogic} logic  - the logic to execute
     * @param {string} contractId - the contract identifier
     * @param {string} clauseName - the clause name
     * @param {object} contract contract data in JSON
     * @param {object} params - the clause parameters
     * @param {object} state - the contract state, a JS object that can be deserialized
     * using the Composer serializer.
     * @param {string} currentTime - the definition of 'now'
     * @return {Promise} a promise that resolves to a result for the clause initialization
     */
    compileAndInvoke(logic, contractId, clauseName, contract, params, state, currentTime) {
        return logic.compileLogic(false).then(() => {
            return this.invoke(logic, contractId, clauseName, contract, params, state, currentTime);
        });
    }

    /**
     * Compile then execute a clause, passing in the request object
     *
     * @param {TemplateLogic} logic  - the logic to execute
     * @param {string} contractId - the contract identifier
     * @param {object} contract - the contract data
     * @param {object} request - the request, a JS object that can be deserialized
     * using the Composer serializer.
     * @param {object} state - the contract state, a JS object that can be deserialized
     * using the Composer serializer.
     * @param {string} currentTime - the definition of 'now'
     * @return {Promise} a promise that resolves to a result for the clause
     */
    compileAndExecute(logic, contractId, contract, request, state, currentTime) {
        return logic.compileLogic(false).then(() => {
            return this.execute(logic, contractId, contract, request, state, currentTime);
        });
    }

}

module.exports = Engine;
