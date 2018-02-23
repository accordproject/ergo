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

const Engine=require("./juracore.js");
const Fs = require('fs');
const Path = require('path');
const moment = require('moment');

const {
    VM,
    VMScript
} = require('vm2');

/**
 * Utility class that implements the internals for Jura.
 * @class
 */
class Jura {
    /**
     * Compile Jura to JavaScript
     *
     * @param {string} path to the Jura file
     * @returns {string} The compiled JavaScript code
     */
    static compileToJavaScript(dslText,contractName,clauseName,withDispatch) {
	// Built-in config
	var config= {
	    'source' : 'jura',
	    'target' : 'javascript',
	    'withdispatch' : withDispatch
	};
	// Clean-up naming for Sexps
	config.jura = dslText;
	if (contractName != null) config.contract = contractName;
	if (clauseName != null) config.clause = clauseName;
	// Call compiler
        return Engine.Jura.compile(config).result;
    }
    /**
     * Compile Jura
     *
     * @param {string} path to the Jura file
     * @returns {object} Promise to the compiled JavaScript code
     */
    static compile(dslText,contractName,clauseName,withDispatch) {
        return Promise.resolve(this.compileToJavaScript(dslText,contractName,clauseName,withDispatch));
    }
    /**
     * Execute Jura
     *
     * @param {string} path to the Jura file
     * @param {object} input data for the clause
     * @param {object} input data for the request transaction
     * @param {string} name of the contract to execute
     * @param {string} name of the clause to execute
     * @returns {object} Promise to the result of execution
     */
    static execute(dslText,jsonClause,jsonRequest,contractName,clauseName,withDispatch) {
	const jurRuntime = Fs.readFileSync(Path.join(__dirname,"juraruntime.js"), 'utf8');
	
        const vm = new VM({
            timeout: 1000,
            sandbox: { moment: moment }
        });

	return (this.compile(dslText,null,null,withDispatch)).then((dslCode) => {
            // add immutables to the context
	    const params = { 'this': jsonClause, 'request': jsonRequest, 'now': moment() };
            vm.freeze(params, 'params'); // Add the context
	    vm.run(jurRuntime); // Load the runtime
	    vm.run(dslCode); // Load the generated logic
	    const contract = 'let contract = new ' + contractName+ '();'; // Instantiate the contract
	    const functionName = 'contract.' + clauseName;
	    const clauseCall = functionName+'(params);'; // Create the clause call
	    const res = vm.run(contract + clauseCall); // Call the logic
	    return res;
	});
    }
}

module.exports = Jura;
