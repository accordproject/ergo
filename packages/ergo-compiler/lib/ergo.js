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

const Engine=require('./ergocore.js');
const CTOParser = require('composer-common/lib/introspect/parser');

/**
 * Utility class that implements the internals for Ergo.
 * @class
 */
class Ergo {
    /**
     * Parse CTO to JSON
     *
     * @param {string} ctoText text for CTO model
     * @returns {object} The parsed CTO model syntax tree in JSON
     */
    static parseCTOToJSON(ctoText) {
        const result = CTOParser.parse(ctoText);
        return result;
    }

    /**
     * Parse CTO
     *
     * @param {string} ctoText text for CTO model
     * @returns {object} The parsed CTO model syntax tree in JSON
     */
    static parseCTO(ctoText) {
        return Promise.resolve(this.parseCTOToJSON(ctoText));
    }

    /**
     * Compile Ergo to JavaScript
     *
     * @param {string} ergoText text for Ergo code
     * @param {string} ctoTexts texts for CTO models
     * @param {string} contractName of the contract to compile
     * @param {string} clauseName of the clause to compile
     * @param {bool} withDispatch whether to generate dispatch function
     * @returns {string} The compiled JavaScript code
     */
    static compileToJavaScript(ergoText,ctoTexts,contractName,clauseName,withDispatch) {
        // Built-in config
        const config= {
            'source' : 'ergo',
            'target' : 'javascript',
            'withdispatch' : withDispatch
        };
        // Clean-up naming for Sexps
        config.ergo = ergoText;
        config.cto = [];
        for (let i = 0; i < ctoTexts.length; i++) {
            config.cto.push(JSON.stringify(this.parseCTOToJSON(ctoTexts[i])));
        }
        if (contractName !== null) { config.contract = contractName; }
        if (clauseName !== null) { config.clause = clauseName; }
        // Call compiler
        const compiled = Engine.Ergo.compile(config);
        if (compiled.error) {
            return { 'error' : compiled.result };
        } else {
            return compiled.result;
        }
    }

    /**
     * Compile Ergo
     *
     * @param {string} ergoText text for Ergo code
     * @param {string} ctoTexts texts for CTO models
     * @param {string} contractName of the contract to compile
     * @param {string} clauseName of the clause to compile
     * @param {bool} withDispatch whether to generate dispatch function
     * @returns {object} Promise to the compiled JavaScript code
     */
    static compile(ergoText,ctoTexts,contractName,clauseName,withDispatch) {
        const result = this.compileToJavaScript(ergoText,ctoTexts,contractName,clauseName,withDispatch);
        return Promise.resolve(result);
    }

}

module.exports = Ergo;
