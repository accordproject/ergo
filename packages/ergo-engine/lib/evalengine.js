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
     * Call to compile a script for a JavaScript machine
     * @param {string} script - the script
     * @return {object} the VM-ready script object
     */
    compileVMScript(script) {
        return script;
    }

    /**
     * Call to execute a call in a JavaScript machine
     * @param {number} utcOffset - UTC Offset for this execution
     * @param {object} now - the definition of 'now'
     * @param {object} options to the text generation
     * @param {object} context - global variables to set in the VM
     * @param {object} script - the initial script to load
     * @param {object} call - the execution call
     * @return {object} the result of execution
     */
    runVMScriptCall(utcOffset,now,options,context,script,call) {
        logger.debug(`Calling eval with context ${context}`);
        const response = eval(script + call);
        return response;
    }

}

module.exports = EvalEngine;
