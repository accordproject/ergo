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

const HyperledgerCTO = Path.join(__dirname,'..','models','org.hyperledger.composer.system.cto');
const ContractCTO = Path.join(__dirname,'..','models','contract.cto');
const MoneyCTO = Path.join(__dirname,'..','models','money.cto');
const RuntimeCTO = Path.join(__dirname,'..','models','runtime.cto');
const CommonCTOs = [HyperledgerCTO, ContractCTO, MoneyCTO, RuntimeCTO];
const CommonCTOTexts = [Fs.readFileSync(HyperledgerCTO, 'utf8'), Fs.readFileSync(ContractCTO, 'utf8'), Fs.readFileSync(MoneyCTO, 'utf8'), Fs.readFileSync(RuntimeCTO, 'utf8')];

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
    static parseCTOtoJSON(ctoText) {
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
        return Promise.resolve(this.parseCTOtoJSON(ctoText));
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
     * @param {string} ergoText text for Ergo code
     * @param {string[]} ctoTexts texts for CTO models
     * @param {string} target language (javascript|javascript_cicero)
     * @returns {string} The compiled JavaScript code
     */
    static compileToJavaScript(ergoText,ctoTexts,target) {
        // Built-in config
        const config= {
            'source' : 'ergo',
            'target' : target
        };
        // Clean-up naming for Sexps
        config.ergo = ergoText;
        const ctos = CommonCTOTexts.concat(ctoTexts);
        config.cto = [];
        for (let i = 0; i < ctos.length; i++) {
            config.cto.push(JSON.stringify(this.parseCTOtoJSON(ctos[i])));
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
     * @param {string} ergoText text for Ergo code
     * @param {string[]} ctoTexts texts for CTO models
     * @param {string} target language (javascript|javascript_cicero)
     * @returns {object} Promise to the compiled and linked JavaScript code
     */
    static compileToJavaScriptAndLink(ergoText,ctoTexts,target) {
        const ergoCode = this.compileToJavaScript(ergoText,ctoTexts,target);
        if (ergoCode.hasOwnProperty('error')) {
            return ergoCode;
        } else {
            return { 'success' : this.linkErgoRuntime(ergoCode.success) };
        }
    }

    /**
     * Compile Ergo
     *
     * @param {string} ergoText text for Ergo code
     * @param {string[]} ctoTexts texts for CTO models
     * @param {string} target language (javascript|javascript_cicero)
     * @returns {object} Promise to the compiled JavaScript code
     */
    static compile(ergoText,ctoTexts,target) {
        const result = this.compileToJavaScript(ergoText,ctoTexts,target);
        return Promise.resolve(result);
    }

    /**
     * Compile and Link Ergo
     *
     * @param {string} ergoText text for Ergo code
     * @param {string[]} ctoTexts texts for CTO models
     * @param {string} target language (javascript|javascript_cicero)
     * @returns {object} Promise to the compiled and linked JavaScript code
     */
    static compileAndLink(ergoText,ctoTexts,target) {
        const result = this.compileToJavaScriptAndLink(ergoText,ctoTexts,target);
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
        switch (error.kind) {
        case 'ParseError':
            return error.message + ' at line ' + error.locstart.line + ' character ' + error.locstart.character;
        default:
            return error.message;
        }
    }

    /**
     * Common CTOs
     *
     * @returns {string[]} Built-in CTO models
     */
    static commonCTOs() {
        return CommonCTOs;
    }
}

module.exports = Ergo;
