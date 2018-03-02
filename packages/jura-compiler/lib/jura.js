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

const Engine=require('./juracore.js');
const Fs = require('fs');
const Path = require('path');
const Moment = require('moment');
const CTOParser = require('composer-common/lib/introspect/parser');

const {
    VM
} = require('vm2');

/**
 * Utility class that implements the internals for Jura.
 * @class
 */
class Jura {
    /**
     * Compile Jura to JavaScript
     *
     * @param {string} juraText text for Jura code
     * @param {string} contractName of the contract to compile
     * @param {string} clauseName of the clause to compile
     * @param {bool} withDispatch whether to generate dispatch function
     * @returns {string} The compiled JavaScript code
     */
    static compileToJavaScript(juraText,contractName,clauseName,withDispatch) {
        // Built-in config
        const config= {
            'source' : 'jura',
            'target' : 'javascript',
            'withdispatch' : withDispatch
        };
        // Clean-up naming for Sexps
        config.jura = juraText;
        if (contractName !== null) { config.contract = contractName; }
        if (clauseName !== null) { config.clause = clauseName; }
        // Call compiler
        const compiled = Engine.Jura.compile(config).result;
        return compiled;
    }

    /**
     * Compile Jura
     *
     * @param {string} juraText text for Jura code
     * @param {string} contractName of the contract to compile
     * @param {string} clauseName of the clause to compile
     * @param {bool} withDispatch whether to generate dispatch function
     * @returns {object} Promise to the compiled JavaScript code
     */
    static compile(juraText,contractName,clauseName,withDispatch) {
        return Promise.resolve(this.compileToJavaScript(juraText,contractName,clauseName,withDispatch));
    }

    /**
     * Execute Jura
     *
     * @param {string} juraText text for Jura code
     * @param {object} clauseJson path to the clause data in JSON
     * @param {object} requestJson path to the request transaction in JSON
     * @param {string} contractName of the contract to execute
     * @param {string} clauseName of the clause to execute
     * @param {bool} withDispatch whether to generate dispatch function
     * @returns {object} Promise to the result of execution
     */
    static execute(juraText,clauseJson,requestJson,contractName,clauseName,withDispatch) {
        const jurRuntime = Fs.readFileSync(Path.join(__dirname,'juraruntime.js'), 'utf8');

        const vm = new VM({
            timeout: 1000,
            sandbox: { moment: Moment }
        });

        return (this.compile(juraText,null,null,withDispatch)).then((juraCode) => {
            // add immutables to the context
            const params = { 'this': clauseJson, 'request': requestJson, 'now': Moment() };
            vm.freeze(params, 'params'); // Add the context
            vm.run(jurRuntime); // Load the runtime
            vm.run(juraCode); // Load the generated logic
            const contract = 'let contract = new ' + contractName+ '();'; // Instantiate the contract
            const functionName = 'contract.' + clauseName;
            const clauseCall = functionName+'(params);'; // Create the clause call
            const res = vm.run(contract + clauseCall); // Call the logic
            return res;
        });
    }

    /**
     * Parse CTO to JSON
     *
     * @param {string} ctoText text for CTO model
     * @returns {object} The parsed CTO model syntax tree in JSON
     */
    static parseCTO(ctoText) {
        const result = CTOParser.parse(ctoText);
        return Promise.resolve(result);
    }

}

module.exports = Jura;
