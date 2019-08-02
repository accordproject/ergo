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
const moment = require('moment-mini');
// Make sure Moment serialization preserves utcOffset. See https://momentjs.com/docs/#/displaying/as-json/
moment.fn.toJSON = Util.momentToJson;

const Engine = require('./engine');

const {
    VM,
    VMScript
} = require('vm2');

/**
 * <p>
 * VMEngine class. Execution of template logic against a request object, returning a response to the caller.
 * This is the vm2-based engine.
 * </p>
 * @class
 * @public
 * @memberof module:ergo-engine
 */
class VMEngine extends Engine {
    /**
     * Engine kind
     * @return {string} which kind of engine
     */
    kind() {
        return 'vm2';
    }

    /**
     * Call to compile a script for a JavaScript machine
     * @param {string} script - the script
     * @return {object} the VM-ready script object
     */
    compileVMScript(script) {
        return new VMScript(script);
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
        const vm = new VM({
            timeout: 1000,
            sandbox: {
                moment: moment,
                logger: Logger,
                utcOffset: utcOffset,
                now: now,
                options: options
            }
        });
        vm.freeze(context, 'context');
        vm.run(script);
        return vm.run(call);
    }

}

module.exports = VMEngine;
