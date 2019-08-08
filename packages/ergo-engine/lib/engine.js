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
const Util = require('@accordproject/ergo-compiler').Util;

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
     * Engine kind
     * @return {string} which kind of engine
     */
    kind() {
        return 'empty';
    }

    /**
    /**
     * Call to compile a script for a JavaScript machine
     * @param {string} script - the script
     */
    compileVMScript(script) {
        throw new Error('[compileVMScript] Cannot execute Engine: instantiate either VMEngine or EvalEngine');
    }

    /**
     * Call to execute a call in a JavaScript machine
     * @param {number} utcOffset - UTC Offset for this execution
     * @param {object} context - global variables to set in the VM
     * @param {object} script - the initial script to load
     * @param {object} call - the execution call
     */
    runVMScriptCall(utcOffset,context,script,call) {
        throw new Error('[runVMScriptCall] Cannot execute Engine: instantiate either VMEngine or EvalEngine');
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
            const script = this.compileVMScript(allJsScripts);
            this.scripts[contractId] = script;
        }
        return this.scripts[contractId];
    }

    /**
     * Execute a clause, passing in the request object
     * @param {LogicManager} logic  - the logic to execute
     * @param {string} contractId - the contract identifier
     * @param {object} contract - the contract data
     * @param {object} request - the request, a JS object that can be deserialized
     * using the Composer serializer.
     * @param {object} state - the contract state, a JS object that can be deserialized
     * using the Composer serializer.
     * @param {string} currentTime - the definition of 'now'
     * @param {object} options to the text generation
     * @return {Promise} a promise that resolves to a result for the clause
     */
    async execute(logic, contractId, contract, request, state, currentTime, options) {
        // Set the current time and UTC Offset
        const now = Util.setCurrentTime(currentTime);
        const utcOffset = now.utcOffset();
        const validOptions = options ? options : {
            options: {
                '$class': 'org.accordproject.markdown.MarkdownOptions',
                'wrapVariables': false,
                'template': false,
            }
        };

        const validContract = logic.validateContract(contract); // ensure the contract is valid
        const validRequest = logic.validateInput(request); // ensure the request is valid
        const validState = logic.validateInput(state); // ensure the state is valid

        Logger.debug('Engine processing request ' + request.$class + ' with state ' + state.$class);

        const script = this.cacheJsScript(logic.getScriptManager(), contractId);
        const callScript = logic.getDispatchCall();

        const context = {
            data: validContract.serialized,
            state: validState,
            request: validRequest
        };

        // execute the logic
        const result = this.runVMScriptCall(utcOffset,now,validOptions,context,script,callScript);

        const validResponse = logic.validateOutput(result.__response); // ensure the response is valid
        const validNewState = logic.validateOutput(result.__state); // ensure the new state is valid
        const validEmit = logic.validateOutputArray(result.__emit); // ensure all the emits are valid

        const answer = {
            'clause': contractId,
            'request': request, // Keep the original request
            'response': validResponse,
            'state': validNewState,
            'emit': validEmit,
        };
        return Promise.resolve(answer);
    }

    /**
     * Invoke a clause, passing in the parameters for that clause
     * @param {LogicManager} logic  - the logic to execute
     * @param {string} contractId - the contract identifier
     * @param {string} clauseName - the clause name
     * @param {object} contract - the contract data
     * @param {object} params - the clause parameters
     * @param {object} state - the contract state, a JS object that can be deserialized
     * using the Composer serializer.
     * @param {string} currentTime - the definition of 'now'
     * @param {object} options to the text generation
     * @return {Promise} a promise that resolves to a result for the clause
     */
    async invoke(logic, contractId, clauseName, contract, params, state, currentTime, options) {
        // Set the current time and UTC Offset
        const now = Util.setCurrentTime(currentTime);
        const utcOffset = now.utcOffset();
        const validOptions = options ? options : {
            options: {
                '$class': 'org.accordproject.markdown.MarkdownOptions',
                'wrapVariables': false,
                'template': false,
            }
        };

        const validContract = logic.validateContract(contract); // ensure the contract is valid
        const validParams = logic.validateInputRecord(params); // ensure the parameters are valid
        const validState = logic.validateInput(state); // ensure the state is valid

        Logger.debug('Engine processing clause ' + clauseName + ' with state ' + state.$class);

        const script = this.cacheJsScript(logic.getScriptManager(), contractId);
        const callScript = logic.getInvokeCall(clauseName);
        const context = {
            data: validContract.serialized,
            state: validState,
            params: validParams
        };

        // execute the logic
        const result = this.runVMScriptCall(utcOffset,now,validOptions,context,script,callScript);

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
        return Promise.resolve(answer);
    }

    /**
     * Initialize a clause
     * @param {LogicManager} logic  - the logic to execute
     * @param {string} contractId - the contract identifier
     * @param {object} contract - the contract data
     * @param {object} params - the clause parameters
     * @param {string} currentTime - the definition of 'now'
     * @param {object} options to the text generation
     * @return {Promise} a promise that resolves to a result for the clause initialization
     */
    async init(logic, contractId, contract, params, currentTime, options) {
        const defaultState = {
            '$class':'org.accordproject.cicero.contract.AccordContractState',
            'stateId':'org.accordproject.cicero.contract.AccordContractState#1'
        };
        return this.invoke(logic, contractId, 'init', contract, params, defaultState, currentTime, options);
    }

    /**
     * Generate Text
     * @param {TemplateLogic} logic  - the logic to execute
     * @param {string} contractId - the contract identifier
     * @param {object} contract - the contract data
     * @param {object} params - the clause parameters
     * @param {string} currentTime - the definition of 'now'
     * @param {object} options to the text generation
     * @return {Promise} a promise that resolves to a result for the clause initialization
     */
    async generateText(logic, contractId, contract, params, currentTime, options) {
        const defaultState = {
            '$class':'org.accordproject.cicero.contract.AccordContractState',
            'stateId':'org.accordproject.cicero.contract.AccordContractState#1'
        };
        return this.invoke(logic, contractId, 'toText', contract, params, defaultState, currentTime, options);
    }

    /**
     * Compile then initialize a clause
     *
     * @param {LogicManager} logic  - the logic to execute
     * @param {object} contract - the contract data
     * @param {object} params - the clause parameters
     * @param {string} currentTime - the definition of 'now'
     * @param {object} options to the text generation
     * @return {Promise} a promise that resolves to a result for the clause initialization
     */
    compileAndInit(logic, contract, params, currentTime, options) {
        return logic.compileLogic(false).then(() => {
            const contractId = logic.getContractName();
            return this.init(logic, contractId, contract, params, currentTime, options);
        });
    }

    /**
     * Compile then generate text
     *
     * @param {TemplateLogic} logic  - the logic to execute
     * @param {object} contract - the contract data
     * @param {object} params - the clause parameters
     * @param {string} currentTime - the definition of 'now'
     * @param {object} options to the text generation
     * @return {Promise} a promise that resolves to a result for the clause initialization
     */
    compileAndGenerateText(logic, contract, params, currentTime, options) {
        return logic.compileLogic(false).then(() => {
            const contractId = logic.getContractName();
            return this.generateText(logic, contractId, contract, params, currentTime, options);
        });
    }

    /**
     * Compile then invoke a clause
     *
     * @param {LogicManager} logic  - the logic to execute
     * @param {string} clauseName - the clause name
     * @param {object} contract contract data in JSON
     * @param {object} params - the clause parameters
     * @param {object} state - the contract state, a JS object that can be deserialized
     * using the Composer serializer.
     * @param {string} currentTime - the definition of 'now'
     * @param {object} options to the text generation
     * @return {Promise} a promise that resolves to a result for the clause initialization
     */
    compileAndInvoke(logic, clauseName, contract, params, state, currentTime, options) {
        return logic.compileLogic(false).then(() => {
            const contractId = logic.getContractName();
            return this.invoke(logic, contractId, clauseName, contract, params, state, currentTime, options);
        });
    }

    /**
     * Compile then execute a clause, passing in the request object
     *
     * @param {LogicManager} logic  - the logic to execute
     * @param {object} contract - the contract data
     * @param {object} request - the request, a JS object that can be deserialized
     * using the Composer serializer.
     * @param {object} state - the contract state, a JS object that can be deserialized
     * using the Composer serializer.
     * @param {string} currentTime - the definition of 'now'
     * @param {object} options to the text generation
     * @return {Promise} a promise that resolves to a result for the clause
     */
    compileAndExecute(logic, contract, request, state, currentTime, options) {
        return logic.compileLogic(false).then(() => {
            const contractId = logic.getContractName();
            return this.execute(logic, contractId, contract, request, state, currentTime, options);
        });
    }

}

module.exports = Engine;
