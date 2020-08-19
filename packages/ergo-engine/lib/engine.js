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

const Logger = require('@accordproject/concerto-core').Logger;
const Util = require('@accordproject/ergo-compiler').Util;
const boxedCollections = require('@accordproject/ergo-compiler').boxedCollections;

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
        this.modules = {};
    }

    /**
     * Engine kind
     * @return {string} which kind of engine
     */
    kind() {
        return undefined;
    }

    /**
     * Engine runtime
     * @return {string} which runtime of engine
     */
    runtime() {
        return undefined;
    }

    /**
    /**
     * instantiate
     * @param {module} module - the module
     */
    async instantiate(module) {
        throw new Error('[instantiate] Cannot instantiate module: create engine for a specific platform');
    }

    /**
     * Execute a call
     * @param {number} utcOffset - UTC Offset for this execution
     * @param {object} context - global variables to set in the VM
     * @param {object} module - the module to load
     * @param {object} call - the execution call
     */
    async invokeCall(utcOffset,context,module,call) {
        throw new Error('[invokeCall] Cannot create invoke call for contract: create engine for a specific platform');
    }

    /**
     * Clear the module cache
     * @private
     */
    clearCache() {
        this.modules = {};
    }

    /**
     * Instantiate and cache the module
     * @param {ScriptManager} scriptManager  - the script manager
     * @param {string} contractId - the contract identifier
     * @return {module} the cached module
     * @private
     */
    async cacheModule(scriptManager, contractId) {
        if (!this.modules[contractId]) {
            const module = scriptManager.getCompiledModule();
            const moduleInstance = await this.instantiate(module);
            this.modules[contractId] = moduleInstance;
        }
        return this.modules[contractId];
    }

    /**
     * Invoke a clause, passing in the parameters for that clause
     * @param {LogicManager} logic  - the logic
     * @param {string} contractId - the contract identifier
     * @param {string} clauseName - the clause name
     * @param {object} contract - the contract data
     * @param {object} params - the clause parameters
     * @param {object} state - the contract state, a JS object that can be deserialized
     * using the Composer serializer.
     * @param {string} currentTime - the definition of 'now'
     * @param {object} options to the text generation
     * @param {object} validateOptions to the validation
     * @return {Promise} a promise that resolves to a result for the clause
     */
    async invoke(logic, contractId, clauseName, contract, params, state, currentTime, options, validateOptions) {
        // Set the current time and UTC Offset
        const now = Util.setCurrentTime(currentTime);
        const utcOffset = now.utcOffset();
        const validOptions = boxedCollections.boxColl(options ? options : {
            '$class': 'org.accordproject.ergo.options.Options',
            'wrapVariables': false,
            'template': false,
        });

        const validContract = logic.validateContract(contract, validateOptions); // ensure the contract is valid
        const validParams = logic.validateInputRecord(params); // ensure the parameters are valid
        const validState = logic.validateInput(state); // ensure the state is valid

        Logger.debug('Engine processing clause ' + clauseName + ' with state ' + state.$class);

        const module = await this.cacheModule(logic.getScriptManager(), contractId);
        const contractName = logic.getContractName();
        const context = {
            data: validContract.serialized,
            state: validState,
            params: validParams,
            __options: validOptions
        };

        // execute the logic
        const wrappedResult = await this.invokeCall(utcOffset,now,validOptions,context,module,contractName,clauseName);
        const result = this.unwrapError(wrappedResult);
        const validResponse = logic.validateOutput(result.__response); // ensure the response is valid
        const validNewState = logic.validateOutput(result.__state); // ensure the new state is valid
        const validEmit = logic.validateOutputArray(result.__emit); // ensure all the emits are valid

        const answer = {
            'clause': contractId,
            'params': params, // Keep the original params
            'response': validResponse,
            'state': validNewState,
            'emit': validEmit,
        };
        return answer;
    }

    /**
     * Initialize a clause
     * @param {LogicManager} logic  - the logic
     * @param {string} contractId - the contract identifier
     * @param {object} contract - the contract data
     * @param {object} params - the clause parameters
     * @param {string} currentTime - the definition of 'now'
     * @param {object} options to the text generation
     * @return {object} the result for the clause initialization
     */
    async init(logic, contractId, contract, params, currentTime, options) {
        const defaultState = {
            '$class':'org.accordproject.cicero.contract.AccordContractState',
            'stateId':'org.accordproject.cicero.contract.AccordContractState#1'
        };
        return await this.invoke(logic, contractId, 'init', contract, params, defaultState, currentTime, options, null);
    }

    /**
     * Trigger a clause, passing in the request object -- trigger means invoking main
     * @param {LogicManager} logic  - the logic
     * @param {string} contractId - the contract identifier
     * @param {object} contract - the contract data
     * @param {object} request - the request, a JS object that can be deserialized
     * using the Composer serializer.
     * @param {object} state - the contract state, a JS object that can be deserialized
     * using the Composer serializer.
     * @param {string} currentTime - the definition of 'now'
     * @param {object} options to the text generation
     * @return {object} the result for the clause
     */
    async trigger(logic, contractId, contract, request, state, currentTime, options) {
        const params = { request: request };
        const answer = await this.invoke(logic, contractId, 'main', contract, params, state, currentTime, options, null);
        // Adjust result for triggers -- replace 'params' by 'request'
        delete answer.params;
        answer.request = request;
        return answer;
    }

    /**
     * Calculate formula
     * @param {TemplateLogic} logic  - the logic
     * @param {string} contractId - the contract identifier
     * @param {string} name - the formula name
     * @param {object} contract - the contract data
     * @param {string} currentTime - the definition of 'now'
     * @param {object} options to the text generation
     * @return {object} the result for draft
     */
    async calculate(logic, contractId, name, contract, currentTime, options) {
        options = options || {};

        const defaultState = {
            '$class':'org.accordproject.cicero.contract.AccordContractState',
            'stateId':'org.accordproject.cicero.contract.AccordContractState#1'
        };
        return await this.invoke(logic, contractId, name, contract, {}, defaultState, currentTime, options, {convertResourcesToId: true});
    }

    /**
     * Compile then initialize a clause
     *
     * @param {LogicManager} logic  - the logic
     * @param {object} contract - the contract data
     * @param {object} params - the clause parameters
     * @param {string} currentTime - the definition of 'now'
     * @param {object} options to the text generation
     * @return {Promise} a promise that resolves to a result for the clause initialization
     */
    async compileAndInit(logic, contract, params, currentTime, options) {
        await logic.compileLogic(false);
        const contractId = logic.getContractName();
        return await this.init(logic, contractId, contract, params, currentTime, options);
    }

    /**
     * Compile then calculate formula
     *
     * @param {TemplateLogic} logic  - the logic
     * @param {string} name - the formula name
     * @param {object} contract - the contract data
     * @param {string} currentTime - the definition of 'now'
     * @param {object} options to the text generation
     * @return {Promise} a promise that resolves to a result for the clause initialization
     */
    async compileAndCalculate(logic, name, contract, currentTime, options) {
        await logic.compileLogic(false);
        const contractId = logic.getContractName();
        return await this.calculate(logic, contractId, name, contract, currentTime, options);
    }

    /**
     * Compile then invoke a clause
     *
     * @param {LogicManager} logic  - the logic
     * @param {string} clauseName - the clause name
     * @param {object} contract contract data in JSON
     * @param {object} params - the clause parameters
     * @param {object} state - the contract state, a JS object that can be deserialized
     * using the Composer serializer.
     * @param {string} currentTime - the definition of 'now'
     * @param {object} options to the text generation
     * @return {Promise} a promise that resolves to a result for the clause initialization
     */
    async compileAndInvoke(logic, clauseName, contract, params, state, currentTime, options) {
        await logic.compileLogic(false);
        const contractId = logic.getContractName();
        return await this.invoke(logic, contractId, clauseName, contract, params, state, currentTime, options, null);
    }

    /**
     * Compile then trigger a clause, passing in the request object
     *
     * @param {LogicManager} logic  - the logic
     * @param {object} contract - the contract data
     * @param {object} request - the request, a JS object that can be deserialized
     * using the Composer serializer.
     * @param {object} state - the contract state, a JS object that can be deserialized
     * using the Composer serializer.
     * @param {string} currentTime - the definition of 'now'
     * @param {object} options to the text generation
     * @return {Promise} a promise that resolves to a result for the clause
     */
    async compileAndTrigger(logic, contract, request, state, currentTime, options) {
        await logic.compileLogic(false);
        const contractId = logic.getContractName();
        return await this.trigger(logic, contractId, contract, request, state, currentTime, options);
    }

    /**
     * Handle success/failure
     * @param {object} result - the result from invokation
     * @return {object} the value if success or throws an error
     */
    unwrapError(result) {
        if (Object.prototype.hasOwnProperty.call(result,'$left')) {
            return result.$left;
        } else {
            const failure = result.$right;
            let message = 'Unknown Ergo Logic Error (Please file a GitHub issue)';
            if (failure && failure.$data && failure.$data.message) {
                message = failure.$data.message;
            }
            throw new Error('[Ergo] ' + message);
        }
    }
}

module.exports = Engine;
