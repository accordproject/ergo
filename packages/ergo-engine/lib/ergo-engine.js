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

const Ergo=require('@accordproject/ergo-compiler/lib/ergo');
const Moment = require('moment');

const {
    VM
} = require('vm2');

/**
 * Utility class that implements the internals for Ergo.
 * @class
 */
class ErgoEngine {
    /**
     * Execute compiled Ergo code
     *
     * @param {string} ergoCode JavaScript code for ergo logic
     * @param {object} contractJson the contract data in JSON
     * @param {object} requestJson the request transaction in JSON
     * @param {object} stateJson the state in JSON
     * @param {string} contractName of the contract to execute
     * @returns {object} Promise to the result of execution
     */
    static executeErgoCode(ergoCode,contractJson,requestJson,stateJson,contractName) {
        const vm = new VM({
            timeout: 1000,
            sandbox: { moment: Moment }
        });

        // add immutables to the context
        const params = { 'contract': contractJson, 'request': requestJson, 'state': stateJson, 'emit': [], 'now': Moment() };
        vm.freeze(params, 'params'); // Add the context
        vm.run(ergoCode); // Load the generated logic
        const contract = 'let contract = new ' + contractName+ '();'; // Instantiate the contract
        const clauseCall = 'contract.main(params);'; // Create the clause call
        const result = vm.run(contract + clauseCall); // Call the logic
        if (result.hasOwnProperty('left')) {
            return Promise.resolve(result.left);
        } else {
            return Promise.resolve({ 'error' : result.right });
        }
    }

    /**
     * Execute Ergo (JavaScript)
     *
     * @param {string} ergoText text for Ergo code
     * @param {string} ctoTexts texts for CTO models
     * @param {object} contractJson the contract data in JSON
     * @param {object} requestJson the request transaction in JSON
     * @param {object} stateJson the state in JSON
     * @param {string} contractName of the contract to execute
     * @returns {object} Promise to the result of execution
     */
    static execute(ergoText,ctoTexts,contractJson,requestJson,stateJson,contractName) {
        return (Ergo.compileAndLink(ergoText,ctoTexts,'javascript')).then((ergoCode) => {
            if (ergoCode.hasOwnProperty('error')) {
                throw new Error(ergoCode.error);
            } else {
                const result =
                      this.executeErgoCode(ergoCode,contractJson,requestJson,stateJson,contractName);
                return result;
            }
        });
    }

}

module.exports = ErgoEngine;
