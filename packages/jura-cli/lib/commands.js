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
const Jura = require('jura-compiler/lib/jura');
const JuraEngine = require('jura-engine/lib/jura-engine');

/**
 * Utility class that implements the commands exposed by the Jura CLI.
 * @class
 */
class Commands {
    /**
     * Compile Jura
     *
     * @param {string} juraPath path to the Jura file
     * @param {string} contractName of the contract to execute
     * @param {string} clauseName of the clause to execute
     * @param {bool} withDispatch whether to generate dispatch function
     * @returns {object} Promise to the compiled JavaScript code
     */
    static compile(juraPath,contractName,clauseName,withDispatch) {
        const jurText = Fs.readFileSync(juraPath, 'utf8');
        return Jura.compile(jurText,contractName,clauseName,withDispatch);
    }

    /**
     * Execute Jura
     *
     * @param {string} juraPath path to the Jura file
     * @param {object} clausePath path to the clause data in JSON
     * @param {object} requestPath path to the request transaction in JSON
     * @param {string} contractName of the contract to execute
     * @param {string} clauseName of the clause to execute
     * @param {bool} withDispatch whether to generate dispatch function
     * @returns {object} Promise to the result of execution
     */
    static execute(juraPath,clausePath,requestPath,contractName,clauseName,withDispatch) {
        const jurText = Fs.readFileSync(juraPath, 'utf8');
        const jsonClause = JSON.parse(Fs.readFileSync(clausePath, 'utf8'));
        const jsonRequest = JSON.parse(Fs.readFileSync(requestPath, 'utf8'));
        return JuraEngine.execute(jurText,jsonClause,jsonRequest,contractName,clauseName,withDispatch);
    }

    /**
     * Parse CTO to JSON
     *
     * @param {string} ctoPath path to CTO model file
     * @returns {object} The parsed CTO model syntax tree in JSON
     */
    static parseCTO(ctoPath) {
        const ctoText = Fs.readFileSync(ctoPath, 'utf8');
        return Jura.parseCTO(ctoText);
    }

}

module.exports = Commands;
