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

/**
 * FunctionDeclaration defines a function that has been defined
 * in a model file. If the name of the function starts with 'on'
 * then the name of the function denotes the name of a transaction
 * declaration that the function processes.
 *
 * @class
 * @memberof module:ergo-compiler
 */
class FunctionDeclaration {

    /**
     * Create a FunctionDeclaration
     *
     * @param {ModelManager} modelManager - the ModelManager used to validate this function
     * @param {string} language - the language that the function is written in. E.g. JS.
     * @param {string} name - the name of the function
     * @param {string} visibility - the visibility of the function
     * @param {string} returnType - the return type of the function
     * @param {string} throws - the type that is thrown by the function
     * @param {string[]} parameterNames - the names of parameters of the function
     * @param {string[]} parameterTypes - the type names of parameters of the function
     * @param {string[]} decorators - the function decorators
     * @param {string} functionText - the function as text
     * @throws {IllegalModelException}
     */
    constructor(modelManager, language, name, visibility, returnType, throws, parameterNames, parameterTypes, decorators, functionText) {

        if(modelManager === null) {
            throw new Error('ModelManager is required.');
        }

        this.modelManager = modelManager;
        this.name = name;
        this.language = language;
        this.visibility = visibility;
        this.returnType = returnType;
        this.throws = throws;
        this.decorators = decorators;
        this.parameterNames = parameterNames;
        this.parameterTypes = parameterTypes;
        this.functionText = functionText;
    }

    /**
     * Returns the text of this function.
     *
     * @return {string} the text that defines the function
     */
    getFunctionText() {
        return this.functionText;
    }

    /**
     * Returns the type thrown by this function
     *
     * @return {string} the type thrown by the function
     */
    getThrows() {
        return this.throws;
    }

    /**
     * Returns the programming language that the function is written in
     *
     * @return {string} the language of the function
     */
    getLanguage() {
        return this.language;
    }

    /**
     * Returns the decorators that the function was tagged with
     *
     * @return {string[]} the @ prefixed decorators for the function
     */
    getDecorators() {
        return this.decorators;
    }

    /**
     * Returns the visibility of this function
     *
     * @return {string} the visibility of the function (+ is public),
     * (- is private)
     */
    getVisibility() {
        return this.visibility;
    }

    /**
     * Returns the return type for this function
     *
     * @return {string} the return type for the function
     */
    getReturnType() {
        return this.returnType;
    }

    /**
     * Returns the name of the function
     *
     * @return {string} the name of the function.
     */
    getName() {
        return this.name;
    }

    /**
     * Returns the names of the parameters processed by the function.
     *
     * @return {string[]} the names of the parameters.
     */
    getParameterNames() {
        return this.parameterNames;
    }

    /**
     * Returns the types of the parameters processed by the function.
     *
     * @return {string[]} the types of the parameters.
     */
    getParameterTypes() {
        return this.parameterTypes;
    }

}

module.exports = FunctionDeclaration;