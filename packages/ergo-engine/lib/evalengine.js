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

const Util = require('@accordproject/ergo-compiler').Util;
const logger = require('@accordproject/ergo-compiler').Logger;
const moment = require('moment-mini');
// Make sure Moment serialization preserves utcOffset. See https://momentjs.com/docs/#/displaying/as-json/
moment.fn.toJSON = Util.momentToJson;

const Engine = require('./engine');

/**
 * <p>
 * EvalEngine class. Execution of template logic against a request object, returning a response to the caller.
 * This is the eval-based engine.
 * </p>
 * @class
 * @public
 * @memberof module:ergo-engine
 */
class EvalEngine extends Engine {
    /**
     * Engine kind
     * @return {string} which kind of engine
     */
    kind() {
        return 'eval';
    }

    /**
     * Engine runtime
     * @return {string} which runtime of engine
     */
    runtime() {
        return 'es6';
    }

    /**
     * Compile a script for a JavaScript machine
     * @param {string} module - the module
     * @return {string} the eval-ready module
     */
    instantiate(module) {
        return module;
    }

    /**
     * Execute a call in a JavaScript machine
     * @param {number} utcOffset - UTC Offset for this execution
     * @param {object} now - the definition of 'now'
     * @param {object} options to the text generation
     * @param {object} context - global variables to set in the VM
     * @param {object} script - the initial script to load
     * @param {object} contractName - the contract name
     * @param {object} clauseName - the clause name in that contract
     * @return {object} the result of execution
     */
    invokeCall(utcOffset,now,options,context,script,contractName,clauseName) {
        const call = this.getInvokeCall(contractName,clauseName);
        logger.debug(`Calling eval with context ${context}`);
        const response = eval(script + call);
        return response;
    }

    /**
     * Generate the invocation logic
     * @param {String} contractName - the contract name
     * @param {String} clauseName - the clause name inside that contract
     * @return {String} the invocation code
     * @private
     */
    getInvokeCall(contractName,clauseName) {
        let code;
        if (contractName) {
            code = `
${contractName}.${clauseName}(Object.assign({}, {__now:now,__options:options,__contract:context.data,__state:context.state,__emit:{$coll:[],$length:0}},context.params));
`;
        } else {
            throw new Error('Cannot invoke contract without a contract name');
        }
        return code;
    }

}

module.exports = EvalEngine;
