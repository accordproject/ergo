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

const loader = require('@assemblyscript/loader');
const bin = require('./binary_encoding.js');

/**
 * Write a value to a module's memory
 * @param {*} mod - module
 * @param {*} value - the value
 * @return {*} the pointer to the value
 */
function write(mod, value) {
    let { __alloc, __retain, memory} = mod.exports;
    let value_bin = bin.ejson_to_bytes(value); // ejson --JS--> binary
    let bytes_ptr = __retain(__alloc(value_bin.byteLength)); // alloc runtime memory
    Buffer.from(value_bin).copy(Buffer.from(memory.buffer, bytes_ptr)); // copy binary value
    return bytes_ptr;
}

/**
 * Read a value from a module's memory
 * @param {*} mod - module
 * @param {*} ptr - pointer to the value
 * @return {*} the value
 */
function read(mod, ptr) {
    let { memory } = mod.exports;
    let value = bin.ejson_of_bytes(memory.buffer, ptr); // binary --JS--> ejson
    return value;
}

/**
 * invoke WASM code
 * @param {*} runtime - the runtime module
 * @param {*} module - the main module
 * @param {string} fn_name - the function to invoke
 * @param {*} arg - the function arguments
 * @return {*} a pointer to the result
 */
async function invoke(runtime, module, fn_name, arg) {
    let rt = await loader.instantiate(runtime);
    let m = await loader.instantiate(module, { runtime: rt.instance.exports });
    let arg_ptr = write(rt, arg);
    let res_ptr = m.exports[fn_name](arg_ptr);
    let res = read(rt, res_ptr);
    return res;
}

/**
 * <p>
 * EvalEngine class. Execution of template logic against a request object, returning a response to the caller.
 * This is the eval-based engine.
 * </p>
 * @class
 * @public
 * @memberof module:ergo-engine
 */
class WasmEngine extends Engine {
    /**
     * Engine kind
     * @return {string} which kind of engine
     */
    kind() {
        return 'wasm';
    }

    /**
     * Engine runtime
     * @return {string} which runtime of engine
     */
    runtime() {
        return 'wasm';
    }

    /**
     * Compile a script for a JavaScript machine
     * @param {string} script - the script
     * @return {object} the VM-ready script object
     */
    compileVMScript(script) {
        return script;
    }

    /**
     * Execute a call in a JavaScript machine
     * @param {number} utcOffset - UTC Offset for this execution
     * @param {object} now - the definition of 'now'
     * @param {object} options to the text generation
     * @param {object} context - global variables to set in the VM
     * @param {object} script - the initial script to load
     * @param {object} call - the execution call
     * @return {object} the result of execution
     */
    async runVMScriptCall(utcOffset,now,options,context,script,call) {
        logger.debug(`Calling eval with context ${context}`);
        const response = await invoke(null, script + call, null, null);
        return response;
    }

}

module.exports = WasmEngine;
