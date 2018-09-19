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
     * Compile Ergo contract
     *
     * @param {string[]} ergoPaths paths to the Ergo modules
     * @param {string[]} ctoPaths paths to CTO models
     * @param {string} target language (es5|es6|cicero|java)
     * @param {boolean} link to JavaScript runtime
     * @returns {object} Promise to the compiled JavaScript code
     */
    static compile(ergoPaths,ctoPaths,target,link) {
        if (typeof ergoPaths === 'undefined') { ergoPaths = []; }
        const ergoSources = [];
        for (let i = 0; i < ergoPaths.length; i++) {
            const ergoFile = ergoPaths[i];
            const ergoContent = Fs.readFileSync(ergoFile, 'utf8');
            ergoSources.push({ 'name': ergoFile, 'content': ergoContent });
        }
        if (typeof ctoPaths === 'undefined') { ctoPaths = []; }
        let ctoSources = [];
        for (let i = 0; i < ctoPaths.length; i++) {
            const ctoFile = ctoPaths[i];
            const ctoContent = Fs.readFileSync(ctoFile, 'utf8');
            ctoSources.push({ 'name': ctoFile, 'content': ctoContent });
        }
        if (link) {
            return Ergo.compileAndLink(ergoSources,ctoSources,target);
        } else  {
            return Ergo.compile(ergoSources,ctoSources,target);
        }
    }

    /**
     * Execute Ergo contract
     *
     * @param {string[]} ergoPaths paths to the Ergo modules
     * @param {string[]} ctoPaths paths to CTO models
     * @param {string} contractPath path to the contract data in JSON
     * @param {string[]} requestsPath path to the request transaction in JSON
     * @param {string} statePath path to the state in JSON
     * @param {string} contractName of the contract to execute
     * @returns {object} Promise to the result of execution
     */
    static execute(ergoPaths,ctoPaths,contractPath,requestsPath,statePath,contractName) {
        if (typeof ergoPaths === 'undefined') { ergoPaths = []; }
        const ergoSources = [];
        for (let i = 0; i < ergoPaths.length; i++) {
            const ergoFile = ergoPaths[i];
            const ergoContent = Fs.readFileSync(ergoFile, 'utf8');
            ergoSources.push({ 'name': ergoFile, 'content': ergoContent });
        }
        if (typeof ctoPaths === 'undefined') { ctoPaths = []; }
        let ctoSources = [];
        for (let i = 0; i < ctoPaths.length; i++) {
            const ctoFile = ctoPaths[i];
            const ctoContent = Fs.readFileSync(ctoFile, 'utf8');
            ctoSources.push({ 'name': ctoFile, 'content': ctoContent });
        }
        const contractJson = JSON.parse(Fs.readFileSync(contractPath, 'utf8'));
        let requestsJson = [];
        for (let i = 0; i < requestsPath.length; i++) {
            requestsJson.push(JSON.parse(Fs.readFileSync(requestsPath[i], 'utf8')));
        }
        const firstRequest = requestsJson[0];
        let initResponse;
        if (statePath === null) {
            initResponse = ErgoEngine.init(ergoSources,ctoSources,'es6',contractJson,firstRequest,contractName);
        } else {
            const stateJson = JSON.parse(Fs.readFileSync(statePath, 'utf8'));
            initResponse = ErgoEngine.execute(ergoSources,ctoSources,'es6',contractJson,firstRequest,stateJson,contractName);
        }
        // Get all the other requests and chain execution through Promise.reduce()
        const otherRequests = requestsJson.slice(1, requestsJson.length);
        return otherRequests.reduce((promise,requestJson) => {
            return promise.then((result) => {
                return ErgoEngine.execute(ergoSources,ctoSources,'es6',contractJson,requestJson,result.state,contractName);
            });
        }, initResponse);
    }

    /**
     * Parse CTO to JSON File
     *
     * @param {string} ctoPath path to CTO model file
     * @returns {string} The name of the generated CTOJ model file
     */
    static parseCTOtoFileSync(ctoPath) {
        const ctoSource = Fs.readFileSync(ctoPath, 'utf8');
        const result = Ergo.parseCTOtoJSON(ctoSource);
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
