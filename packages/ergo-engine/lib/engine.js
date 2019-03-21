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
const ResourceValidator = require('composer-concerto/lib/serializer/resourcevalidator');

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
     * @private
     */
    compileJsLogic(scriptManager, contractId) {
        let allJsScripts = '';

        scriptManager.getAllScripts().forEach(function (element) {
            if (element.getLanguage() === '.js') {
                allJsScripts += element.getContents();
            }
        }, this);

        if (allJsScripts === '') {
            throw new Error('Did not find any JavaScript logic');
        }

        //console.log('SCRIPT!!!!\n' + allJsScripts);
        const script = new VMScript(allJsScripts);
        this.scripts[contractId] = script;
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
        const serializer = logic.getSerializer();
        const scriptManager = logic.getScriptManager();

        // ensure the contract is valid
        const validContract = serializer.fromJSON(contract, {validate: false, acceptResourcesForRelationships: true});
        validContract.$validator = new ResourceValidator({permitResourcesForRelationships: true});
        validContract.validate();

        // ensure the request is valid
        const validRequest = serializer.fromJSON(request, {validate: false, acceptResourcesForRelationships: true});
        validRequest.$validator = new ResourceValidator({permitResourcesForRelationships: true});
        validRequest.validate();

        // Set the current time and UTC Offset
        const now = Util.setCurrentTime(currentTime);
        const utcOffset = now.utcOffset();

        // ensure the state is valid
        const validState = serializer.fromJSON(state, {validate: false, acceptResourcesForRelationships: true});
        validState.$validator = new ResourceValidator({permitResourcesForRelationships: true});
        validState.validate();

        Logger.debug('Engine processing request ' + request.$class + ' with state ' + state.$class);

        let script;

        this.compileJsLogic(scriptManager, contractId);
        script = this.scripts[contractId];

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
        vm.freeze(serializer.toJSON(validContract, {permitResourcesForRelationships:true}), 'data');
        vm.freeze(serializer.toJSON(validState, {permitResourcesForRelationships:true}), 'state');
        vm.freeze(now, 'now');
        vm.freeze(serializer.toJSON(validRequest, {permitResourcesForRelationships:true}), 'request');

        // execute the logic
        vm.run(script);
        const ergoResult = vm.run(callScript);

        let result;
        if (ergoResult.hasOwnProperty('left')) {
            result = ergoResult.left;
        } else if (ergoResult.hasOwnProperty('right')) {
            throw new Error('[Ergo] ' + JSON.stringify(ergoResult.right));
        } else {
            result = ergoResult;
        }

        // ensure the response is valid
        let responseResult = null;
        if (result.response) {
            const validResponse = serializer.fromJSON(result.response, {validate: false, acceptResourcesForRelationships: true});
            validResponse.$validator = new ResourceValidator({permitResourcesForRelationships: true});
            validResponse.validate();
            responseResult = serializer.toJSON(validResponse, {convertResourcesToRelationships: true});
        }

        // ensure the new state is valid
        const validNewState = serializer.fromJSON(result.state, {validate: false, acceptResourcesForRelationships: true});
        validNewState.$validator = new ResourceValidator({permitResourcesForRelationships: true});
        validNewState.validate();
        const stateResult = serializer.toJSON(validNewState, {convertResourcesToRelationships: true});

        // ensure all the emits are valid
        let emitResult = [];
        for (let i = 0; i < result.emit.length; i++) {
            const validEmit = serializer.fromJSON(result.emit[i], {validate: false, acceptResourcesForRelationships: true});
            validEmit.$validator = new ResourceValidator({permitResourcesForRelationships: true});
            validEmit.validate();
            emitResult.push(serializer.toJSON(validEmit, {convertResourcesToRelationships: true}));
        }

        return {
            'clause': contractId,
            'request': request,
            'response': responseResult,
            'state': stateResult,
            'emit': emitResult,
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
        const serializer = logic.getSerializer();
        const scriptManager = logic.getScriptManager();

        // ensure the contract is valid
        const validContract = serializer.fromJSON(contract, {validate: false, acceptResourcesForRelationships: true});
        validContract.$validator = new ResourceValidator({permitResourcesForRelationships: true});
        validContract.validate();

        // ensure the parameters are valid
        let validParams = {};
        for(const key in params) {
            if (params[key] instanceof Object) {
                const validParam = serializer.fromJSON(params[key], {validate: false, acceptResourcesForRelationships: true});
                validParam.$validator = new ResourceValidator({permitResourcesForRelationships: true});
                validParam.validate();
                validParams[key] = serializer.toJSON(validParam, {permitResourcesForRelationships:true});
            } else {
                validParams[key] = params[key];
            }
        }

        // Set the current time and UTC Offset
        const now = Util.setCurrentTime(currentTime);
        const utcOffset = now.utcOffset();

        // ensure the state is valid
        const validState = serializer.fromJSON(state, {validate: false, acceptResourcesForRelationships: true});
        validState.$validator = new ResourceValidator({permitResourcesForRelationships: true});
        validState.validate();

        Logger.debug('Engine processing clause ' + clauseName + ' with state ' + state.$class);

        let script;

        this.compileJsLogic(scriptManager, contractId);
        script = this.scripts[contractId];

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
        vm.freeze(serializer.toJSON(validContract, {permitResourcesForRelationships:true}), 'data');
        vm.freeze(serializer.toJSON(validState, {permitResourcesForRelationships:true}), 'state');
        vm.freeze(now, 'now');
        vm.freeze(validParams, 'params');

        // execute the logic
        vm.run(script);
        const ergoResult = vm.run(callScript);

        let result;
        if (ergoResult.hasOwnProperty('left')) {
            result = ergoResult.left;
        } else if (ergoResult.hasOwnProperty('right')) {
            throw new Error('[Ergo] ' + JSON.stringify(ergoResult.right));
        } else {
            result = ergoResult;
        }

        // ensure the response is valid
        let responseResult = null;
        if (result.response) {
            const validResponse = serializer.fromJSON(result.response, {validate: false, acceptResourcesForRelationships: true});
            validResponse.$validator = new ResourceValidator({permitResourcesForRelationships: true});
            validResponse.validate();
            responseResult = serializer.toJSON(validResponse, {convertResourcesToRelationships: true});
        }

        // ensure the new state is valid
        const validNewState = serializer.fromJSON(result.state, {validate: false, acceptResourcesForRelationships: true});
        validNewState.$validator = new ResourceValidator({permitResourcesForRelationships: true});
        validNewState.validate();
        const stateResult = serializer.toJSON(validNewState, {convertResourcesToRelationships: true});

        // ensure all the emits are valid
        let emitResult = [];
        for (let i = 0; i < result.emit.length; i++) {
            const validEmit = serializer.fromJSON(result.emit[i], {validate: false, acceptResourcesForRelationships: true});
            validEmit.$validator = new ResourceValidator({permitResourcesForRelationships: true});
            validEmit.validate();
            emitResult.push(serializer.toJSON(validEmit, {convertResourcesToRelationships: true}));
        }

        return {
            'clause': contractId,
            'params': params,
            'response': responseResult,
            'state': stateResult,
            'emit': emitResult,
        };
    }

    /**
     * Initialize a clause
     * @param {TemplateLogic} logic  - the logic to execute
     * @param {string} contractId - the contract identifier
     * @param {object} contract - the contract data
     * @param {string} currentTime - the definition of 'now'
     * @return {Promise} a promise that resolves to a result for the clause initialization
     */
    async init(logic, contractId, contract, currentTime) {
        const serializer = logic.getSerializer();
        const scriptManager = logic.getScriptManager();

        // ensure the contract is valid
        const validContract = serializer.fromJSON(contract, {validate: false, acceptResourcesForRelationships: true});
        validContract.$validator = new ResourceValidator({permitResourcesForRelationships: true});
        validContract.validate();

        // Set the current time and UTC Offset
        const now = Util.setCurrentTime(currentTime);
        const utcOffset = now.utcOffset();

        let script;

        this.compileJsLogic(scriptManager, contractId);
        script = this.scripts[contractId];

        const callScript = logic.getInitCall();

        const vm = new VM({
            timeout: 1000,
            sandbox: {
                moment: Moment,
                logger: Logger,
                utcOffset: utcOffset
            }
        });

        // add immutables to the context
        vm.freeze(serializer.toJSON(validContract, {permitResourcesForRelationships:true}), 'data');
        vm.freeze(now, 'now');

        // execute the logic
        //console.log(script);
        vm.run(script);
        const ergoResult = vm.run(callScript);

        let result;
        if (ergoResult.hasOwnProperty('left')) {
            result = ergoResult.left;
        } else if (ergoResult.hasOwnProperty('right')) {
            throw new Error('[Ergo] ' + JSON.stringify(ergoResult.right));
        } else {
            result = ergoResult;
        }

        // ensure the response is valid
        let responseResult = null;
        if (result.response) {
            const validResponse = serializer.fromJSON(result.response, {validate: false, acceptResourcesForRelationships: true});
            validResponse.$validator = new ResourceValidator({permitResourcesForRelationships: true});
            validResponse.validate();
            responseResult = serializer.toJSON(validResponse, {convertResourcesToRelationships: true});
        }
        //console.log('RESULT!!! ' + JSON.stringify(responseResult));
        // ensure the response is valid

        // ensure the new state is valid
        const validNewState = serializer.fromJSON(result.state, {validate: false, acceptResourcesForRelationships: true});
        validNewState.$validator = new ResourceValidator({permitResourcesForRelationships: true});
        validNewState.validate();
        const stateResult = serializer.toJSON(validNewState, {convertResourcesToRelationships: true});

        // ensure all the emits are valid
        let emitResult = [];
        for (let i = 0; i < result.emit.length; i++) {
            const validEmit = serializer.fromJSON(result.emit[i], {validate: false, acceptResourcesForRelationships: true});
            validEmit.$validator = new ResourceValidator({permitResourcesForRelationships: true});
            validEmit.validate();
            emitResult.push(serializer.toJSON(validEmit, {convertResourcesToRelationships: true}));
        }

        return {
            'clause': contractId,
            'request': null,
            'response': responseResult,
            'state': stateResult,
            'emit': emitResult,
        };
    }

    /**
     * Compile then initialize a clause
     *
     * @param {TemplateLogic} logic  - the logic to execute
     * @param {string} contractId - the contract identifier
     * @param {object} contract - the contract data
     * @param {string} currentTime - the definition of 'now'
     * @return {Promise} a promise that resolves to a result for the clause initialization
     */
    compileAndInit(logic, contractId, contract, currentTime) {
        return logic.compileLogic(false).then(() => {
            return this.init(logic, contractId, contract, currentTime);
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
