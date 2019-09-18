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

const CompilerCore=require('../extracted/compilercore');
const CTOParser = require('@accordproject/concerto/lib/introspect/parser');
const Logger = require('@accordproject/markdown-common').Logger;

/**
 * <p>
 * Compiler class. Compilation for Ergo logic.
 * </p>
 * @class
 * @public
 * @memberof module:ergo-compiler
 */
class Compiler {
    /**
     * Parse CTO to JSON
     *
     * @param {string} ctoContent for CTO model
     * @returns {object} The parsed CTO model syntax tree in JSON
     */
    static parseCTOtoJSON(ctoContent) {
        const result = CTOParser.parse(ctoContent);
        return result;
    }

    /**
     * Contract call name
     *
     * @param {string} contractName name of the contract
     * @returns {string} name of the JavaScript class
     */
    static contractCallName(contractName) {
        return CompilerCore.call({ 'name' : contractName });
    }

    /**
     * Contract call name promise
     *
     * @param {string} contractName name of the contract
     * @returns {string} a promise to the name of the compiled JavaScript class
     */
    static contractCallNamePromise(contractName) {
        return Promise.resolve(this.contractCallName(contractName));
    }

    /**
     * Compile Ergo to JavaScript
     *
     * @param {Array<{name:string, content:string}>} ergoSources Ergo modules
     * @param {Array<{name:string, content:string}>} ctoSources CTO models
     * @param {string} sourceTemplate - an optional template source
     * @param {string} target language (es5|es6|cicero|java)
     * @param {boolean} link whether to link the javascript runtime
     * @param {boolean} warnings whether to print warnings
     * @returns {string} The compiled JavaScript code
     */
    static compileToJavaScript(ergoSources,ctoSources,sourceTemplate,target,link,warnings) {
        // Built-in config
        const config= {
            'source' : 'ergo',
            'target' : target,
            'link' : link
        };
        config.sourceTemplate = sourceTemplate ? sourceTemplate : null;
        config.ergo = [];
        for (let i = 0; i < ergoSources.length; i++) {
            config.ergo.push(ergoSources[i]);
        }
        config.cto = [];
        for (let i = 0; i < ctoSources.length; i++) {
            let ctoFile = ctoSources[i].name;
            let ctoContent = ctoSources[i].content;
            config.cto.push({ 'name' : ctoFile, 'content' : JSON.stringify(this.parseCTOtoJSON(ctoContent)) });
        }
        // Call compiler
        const compiled = CompilerCore.compile(config);
        if (warnings) { compiled.warnings.map((w) => { Logger.warn(w); } ); }
        if (compiled.code) {
            return { 'error' : compiled.error };
        } else {
            return { 'success' : compiled.result, 'contractName' : compiled.contractName };
        }
    }

    /**
     * Compile Ergo
     *
     * @param {Array<{name:string, content:string}>} ergoSources Ergo modules
     * @param {Array<{name:string, content:string}>} ctoSources CTO models
     * @param {string} sourceTemplate - an optional template source
     * @param {string} target language (es5|es6|cicero|java)
     * @param {boolean} link whether to link the javascript runtime
     * @param {boolean} warnings whether to print warnings
     * @returns {object} Promise to the compiled JavaScript code
     */
    static compile(ergoSources,ctoSources,sourceTemplate,target,link,warnings) {
        const result = this.compileToJavaScript(ergoSources,ctoSources,sourceTemplate,target,link,warnings);
        return Promise.resolve(result);
    }

    /**
     * Error message
     *
     * @param {object} error object returned by Ergo compiler
     * @returns {string} error message
     */
    static ergoErrorToString(error) {
        return error.message;
    }

    /**
     * Error message (verbose)
     *
     * @param {object} error object returned by Ergo compiler
     * @returns {string} verbose error message
     */
    static ergoVerboseErrorToString(error) {
        return error.fullMessage;
    }


    /**
     * Available compiler targets
     * @return {Array<string>} the available compilation targets for the logic
     */
    static availableTargets() {
        return CompilerCore.availabletargets();
    }

    /**
     * Is valid compiler target
     * @param {string} target - the target
     * @return {boolean} whether the target is valid
     */
    static isValidTarget(target) {
        const available = this.availableTargets();
        if (available.includes(target)) {
            return true;
        } else {
            throw new Error(`Unknown target: ${target} (available: ${available})`);
        }
    }
}

module.exports = Compiler;
