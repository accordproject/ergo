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
const Ergo = require('@accordproject/ergo-compiler/lib/ergo');
const ErgoEngine = require('@accordproject/ergo-engine/lib/ergo-engine');

/**
 * Utility class that implements the commands exposed by the Ergo CLI.
 * @class
 */
class Commands {
    /**
     * Compile Ergo
     *
     * @param {string} ergoPath path to the Ergo file
     * @param {string} ctoPaths paths to CTO models
     * @param {bool} withDispatch whether to generate dispatch function
     * @returns {object} Promise to the compiled JavaScript code
     */
    static compile(ergoPath,ctoPaths,withDispatch) {
        const ergoText = Fs.readFileSync(ergoPath, 'utf8');
        if (typeof ctoPaths === 'undefined') { ctoPaths = []; }
        let ctoTexts = [];
        for (let i = 0; i < ctoPaths.length; i++) {
            const ctoText = Fs.readFileSync(ctoPaths[i], 'utf8');
            ctoTexts.push(ctoText);
        }
        return Ergo.compile(ergoText,ctoTexts,withDispatch);
    }

    /**
     * Execute Ergo
     *
     * @param {string} ergoPath path to the Ergo file
     * @param {string} ctoPaths paths to CTO models
     * @param {object} contractPath path to the contract data in JSON
     * @param {object} requestPath path to the request transaction in JSON
     * @param {object} statePath path to the state in JSON
     * @param {string} contractName of the contract to execute
     * @param {string} clauseName of the clause to execute
     * @param {bool} withDispatch whether to generate dispatch function
     * @returns {object} Promise to the result of execution
     */
    static execute(ergoPath,ctoPaths,contractPath,requestPath,statePath,contractName,clauseName,withDispatch) {
        const ergoText = Fs.readFileSync(ergoPath, 'utf8');
        if (typeof ctoPaths === 'undefined') { ctoPaths = []; }
        let ctoTexts = [];
        for (let i = 0; i < ctoPaths.length; i++) {
            const ctoText = Fs.readFileSync(ctoPaths[i], 'utf8');
            ctoTexts.push(ctoText);
        }
        const contractJson = JSON.parse(Fs.readFileSync(contractPath, 'utf8'));
        const requestJson = JSON.parse(Fs.readFileSync(requestPath, 'utf8'));
        const stateJson = JSON.parse(Fs.readFileSync(statePath, 'utf8'));
        return ErgoEngine.execute(ergoText,ctoTexts,contractJson,requestJson,stateJson,contractName,clauseName,withDispatch);
    }

    /**
     * Parse CTO to JSON
     *
     * @param {string} ctoPath path to CTO model file
     * @returns {object} The parsed CTO model syntax tree in JSON
     */
    static parseCTO(ctoPath) {
        const ctoText = Fs.readFileSync(ctoPath, 'utf8');
        return Ergo.parseCTO(ctoText);
    }

    /**
     * Parse CTO to JSON File
     *
     * @param {string} ctoPath path to CTO model file
     * @returns {string} The name of the generated CTOJ model file
     */
    static parseCTOtoFileSync(ctoPath) {
        const ctoText = Fs.readFileSync(ctoPath, 'utf8');
        const result = Ergo.parseCTOtoJSON(ctoText);
        const outFile = ctoPath.substr(0, ctoPath.lastIndexOf('.')) + '.ctoj';
        Fs.writeFileSync(outFile, JSON.stringify(result));
        return outFile;
    }

    /**
     * Parse CTO to JSON File
     *
     * @param {string} ctoPath path to CTO model file
     * @returns {string} The name of the generated CTOJ model file
     */
    static parseCTOtoFile(ctoPath) {
        return Promise.resolve(this.parseCTOtoFileSync(ctoPath));
    }
}

module.exports = Commands;
