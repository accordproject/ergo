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
const CTOParser = require('composer-common/lib/introspect/parser');

/**
 * Utility class that implements the internals for Jura.
 * @class
 */
class Jura {
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
     * Compile Jura to JavaScript
     *
     * @param {string} juraText text for Jura code
     * @param {string} ctoText text for CTO model
     * @param {string} contractName of the contract to compile
     * @param {string} clauseName of the clause to compile
     * @param {bool} withDispatch whether to generate dispatch function
     * @returns {string} The compiled JavaScript code
     */
    static compileToJavaScript(juraText,ctoText,contractName,clauseName,withDispatch) {
        // Built-in config
        const config= {
            'source' : 'jura',
            'target' : 'javascript',
            'withdispatch' : withDispatch
        };
        // Clean-up naming for Sexps
        config.jura = juraText;
        config.cto = JSON.stringify(this.parseCTOToJSON(ctoText));
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
     * @param {string} ctoText text for CTO model
     * @param {string} contractName of the contract to compile
     * @param {string} clauseName of the clause to compile
     * @param {bool} withDispatch whether to generate dispatch function
     * @returns {object} Promise to the compiled JavaScript code
     */
    static compile(juraText,ctoText,contractName,clauseName,withDispatch) {
        return Promise.resolve(this.compileToJavaScript(juraText,ctoText,contractName,clauseName,withDispatch));
    }

}

module.exports = Jura;
