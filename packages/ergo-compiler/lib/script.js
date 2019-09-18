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

const FunctionDeclaration = require('./functiondeclaration');
const JavaScriptParser = require('@accordproject/concerto/lib/codegen/javascriptparser');
const debug = require('debug')('cicero:Script');

/**
 * <p>
 * An executable script.
 * </p>
 * @private
 * @class
 * @memberof module:ergo-compiler
 */
class Script {

    /**
     * Create the Script.
     * <p>
     * @param {ModelManager} modelManager - The ModelManager associated with this Script
     * @param {string} identifier - The identifier of the script
     * @param {string} language - The language type of the script
     * @param {string} contents - The contents of the script
     * @param {string} contractName - The name of the contract if known or null
     */
    constructor(modelManager, identifier, language, contents, contractName) {
        this.modelManager = modelManager;
        this.identifier = identifier;
        this.contractName = contractName;
        this.language = language;
        this.contents = contents;
        this.functions = [];
        this.tokens = [];

        if(!contents) {
            throw new Error('Empty script contents');
        }
        if (this.language === '.js') {
            let data = {errorStatement:''};
            let parser;

            try {
                parser = new JavaScriptParser(this.contents, false, 8);
            } catch (cause) {
                // consider adding a toHex method in the exception to put out the pure hex values of the file.
                const error = new SyntaxError('Failed to parse ' + this.identifier + ': ' + cause.message+'\n'+data.errorStatement);
                error.cause = cause;
                debug('constructor', error.message, contents);
                throw error;
            }

            const functions = parser.getFunctions();

            for(let n=0; n < functions.length; n++) {
                const func = functions[n];
                const functionDeclaration =
                      new FunctionDeclaration(this.modelManager, this.language,
                          func.name, func.visibility,
                          func.returnType, func.throws, func.parameterNames,
                          func.parameterTypes, func.decorators, func.functionText );
                this.functions.push( functionDeclaration );
            }

            this.tokens = parser.getTokens();

            if (!this.getContractName()) {
                let classNames = parser.getClasses().map(x => x.name);
                if (classNames.length !== 0) {
                    this.contractName = classNames[0];
                }
            }
        }
    }

    /**
     * Returns the identifier of the script
     * @return {string} the identifier of the script
     */
    getIdentifier() {
        return this.identifier;
    }

    /**
     * Returns the name of the contract for this script
     * @return {string} the name of the contract, if known
     */
    getContractName() {
        return this.contractName;
    }

    /**
     * Returns the language of the script
     * @return {string} the language of the script
     */
    getLanguage() {
        return this.language;
    }

    /**
     * Returns the contents of the script
     * @return {string} the content of the script
     */
    getContents() {
        return this.contents;
    }

    /**
     * Returns the FunctionDeclaration for all functions that have been defined in this
     * Script.
     *
     * @return {FunctionDeclaration[]} The array of FunctionDeclarations
     */
    getFunctionDeclarations() {
        return this.functions;
    }

    /**
     * Returns the tokens of the script
     * @return {Object[]} the tokens of the script
     */
    getTokens() {
        return this.tokens;
    }

}

module.exports = Script;
