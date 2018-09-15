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
const Path = require('path');
const Compiler=require('./ergo-core.js');
const CTOParser = require('composer-common/lib/introspect/parser');

/**
 * Utility class that implements the internals for Ergo.
 * @class
 */
class Ergo {
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
        return Compiler.call({ 'name' : contractName });
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
     * @param {string} target language (javascript|javascript_cicero)
     * @returns {string} The compiled JavaScript code
     */
    static compileToJavaScript(ergoSources,ctoSources,target) {
        // Built-in config
        const config= {
            'source' : 'ergo',
            'target' : target
        };
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
        const compiled = Compiler.compile(config);
        if (compiled.code) {
            return { 'error' : compiled.error };
        } else {
            return { 'success' : compiled.result };
        }
    }

    /**
     * Compile and Link Ergo to JavaScript
     *
     * @param {Array<{name:string, content:string}>} ergoSources texts for Ergo modules
     * @param {Array<{name:string, content:string}>} ctoSources texts for CTO models
     * @param {string} target language (javascript|javascript_cicero)
     * @returns {object} Promise to the compiled and linked JavaScript code
     */
    static compileToJavaScriptAndLink(ergoSources,ctoSources,target) {
        const ergoCode = this.compileToJavaScript(ergoSources,ctoSources,target);
        if (ergoCode.hasOwnProperty('error')) {
            return ergoCode;
        } else {
            return { 'success' : this.linkErgoRuntime(ergoCode.success) };
        }
    }

    /**
     * Compile Ergo
     *
     * @param {Array<{name:string, content:string}>} ergoSources Ergo modules
     * @param {Array<{name:string, content:string}>} ctoSources CTO models
     * @param {string} target language (javascript|javascript_cicero)
     * @returns {object} Promise to the compiled JavaScript code
     */
    static compile(ergoSources,ctoSources,target) {
        const result = this.compileToJavaScript(ergoSources,ctoSources,target);
        return Promise.resolve(result);
    }

    /**
     * Compile and Link Ergo
     *
     * @param {Array<{name:string, content:string}>} ergoSources Ergo modules
     * @param {Array<{name:string, content:string}>} ctoSources CTO models
     * @param {string} target language (javascript|javascript_cicero)
     * @returns {object} Promise to the compiled and linked JavaScript code
     */
    static compileAndLink(ergoSources,ctoSources,target) {
        const result = this.compileToJavaScriptAndLink(ergoSources,ctoSources,target);
        return Promise.resolve(result);
    }

    /**
     * Link runtime to compiled Ergo code
     *
     * @param {string} ergoCode compiled Ergo code in JavaScript
     * @returns {string} compiled Ergo code in JavaScript linked to Ergo runtime
     */
    static linkErgoRuntime(ergoCode) {
        const ergoRuntime = Fs.readFileSync(Path.join(__dirname,'ergo-runtime.js'), 'utf8');
        return ergoRuntime + '\n' + ergoCode;
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
        return error.verbose;
    }

}

module.exports = Ergo;
