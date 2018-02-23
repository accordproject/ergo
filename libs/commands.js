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

const Fs = require('fs');
const Jura = require('./jura');

/**
 * Utility class that implements the commands exposed by the Jura CLI.
 * @class
 */
class Commands {
    /**
     * Compile Jura
     *
     * @param {string} path to the Jura file
     * @param {string} name of the contract to execute
     * @param {string} name of the clause to execute
     * @param {bool} whether to generate dispatch function
     * @returns {object} Promise to the compiled JavaScript code
     */
    static compile(dslPath,contractName,clauseName,withDispatch) {
        const jurText = Fs.readFileSync(dslPath, 'utf8');
	return Jura.compile(jurText,contractName,clauseName,withDispatch);
    }

    /**
     * Execute Jura
     *
     * @param {string} path to the Jura file
     * @param {object} input data for the clause
     * @param {object} input data for the request transaction
     * @param {string} name of the contract to execute
     * @param {string} name of the clause to execute
     * @param {bool} whether to generate dispatch function
     * @returns {object} Promise to the result of execution
     */
    static execute(dslPath,clausePath,requestPath,contractName,clauseName,withDispatch) {
        const jurText = Fs.readFileSync(dslPath, 'utf8');
        const jsonClause = JSON.parse(Fs.readFileSync(clausePath, 'utf8'));
        const jsonRequest = JSON.parse(Fs.readFileSync(requestPath, 'utf8'));
	return Jura.execute(jurText,jsonClause,jsonRequest,contractName,clauseName,withDispatch);
    }
}

module.exports = Commands;
