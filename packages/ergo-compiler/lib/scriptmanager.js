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

const Script = require('./script');
const ErgoCompiler = require('./compiler');

/**
 * <p>
 * Manages a set of scripts.
 * </p>
 * @private
 * @class
 * @memberof module:ergo-compiler
 */
class ScriptManager {

    /**
     * Create the ScriptManager.
     * <p>
     * <strong>Note: Only to be called by framework code. Applications should
     * retrieve instances from {@link BusinessNetworkDefinition}</strong>
     * </p>
     * @param {String} target  - compiler target (either: 'cicero', 'es5', 'es6', or 'java')
     * @param {ModelManager} modelManager - The ModelManager to use for this ScriptManager
     */
    constructor(target, modelManager) {
        this.target = target;
        this.modelManager = modelManager;
        this.scripts = {};
        this.compiledScript = null;
    }

    /**
     * Visitor design pattern
     * @param {Object} visitor - the visitor
     * @param {Object} parameters  - the parameter
     * @return {Object} the result of visiting or null
     * @private
     */
    accept(visitor,parameters) {
        return visitor.visit(this, parameters);
    }

    /**
     * Change the compilation target. Note: This might force recompilation if logic has already been compiled.
     * @param {String} target - compiler target (either: 'cicero', 'es5', 'es6', or 'java')
     * @param {boolean} recompile - whether to force recompilation of the logic
     */
    changeTarget(target, recompile) {
        this.target = target;
        if (recompile) { this.compileLogic(true); }
    }

    /**
     * Creates a new Script from a string.
     *
     * @param {string} identifier - the identifier of the script
     * @param {string} language - the language identifier of the script
     * @param {string} contents - the contents of the script
     * @returns {Script} - the instantiated script
     */
    createScript(identifier, language, contents) {
        return new Script(this.modelManager, identifier, language, contents);
    }

    /**
     * Modify an existing Script from a string.
     *
     * @param {string} identifier - the identifier of the script
     * @param {string} language - the language identifier of the script
     * @param {string} contents - the contents of the script
     */
    modifyScript(identifier, language, contents) {
        this.updateScript(new Script(this.modelManager, identifier, language, contents));
    }

    /**
     * Adds a Script to the ScriptManager
     * @param {Script} script - The script to add to the ScriptManager
     */
    addScript(script) {
        this.scripts[script.getIdentifier()] = script;
    }

    /**
     * Update an existing Script in the ScriptManager
     * @param {Script} script - The script to add to the ScriptManager
     */
    updateScript(script) {
        if (!this.scripts[script.getIdentifier()]) {
            throw new Error('Script file does not exist');
        }
        this.addScript(script);
        // Re-compile Ergo
        this.compileLogic(true);
    }

    /**
     * Remove the Script
     * @param {string} identifier - The identifier of the script to remove
     * delete.
     */
    deleteScript(identifier) {
        if (!this.scripts[identifier]) {
            throw new Error('Script file does not exist');
        }
        delete this.scripts[identifier];
    }

    /**
     * Get the array of Script instances
     * @return {Script[]} The Scripts registered
     * @private
     */
    getScripts() {
        let keys = Object.keys(this.scripts);
        let result = [];

        for(let n=0; n < keys.length;n++) {
            result.push(this.scripts[keys[n]]);
        }

        return result;
    }

    /**
     * Get the array of all Script instances, including compiled ones
     * @return {Script[]} The Scripts registered, including compiled ones
     * @private
     */
    getAllScripts() {
        let result = this.getScripts();
        if (this.compiledScript !== null) {
            result.push(this.compiledScript);
        }
        return result;
    }

    /**
     * Get the array of Script instances for the given language
     * @param {string} language - The scripts' language
     * @return {Script[]} The Scripts registered
     * @private
     */
    getScriptsForLanguage(language) {
        let keys = Object.keys(this.scripts);
        let result = [];

        for(let n=0; n < keys.length;n++) {
            if (this.scripts[keys[n]].getLanguage() === language)  {
                result.push(this.scripts[keys[n]]);
            }
        }

        return result;
    }

    /**
     * Gets all the Ergo logic
     * @return {Array<{name:string, content:string}>} the name and content of each Ergo file
     */
    getLogic() {
        let logic = [];
        const scripts = this.getScriptsForLanguage('.ergo');
        scripts.forEach(function (script) {
            logic.push({ 'name' : script.getName(), 'content' : script.getContents() });
        });
        return logic;
    }

    /**
     * Remove all registered Composer files
     */
    clearScripts() {
        this.scripts = {};
        this.compiledScript = null;
    }

    /**
     * Get the Script associated with an identifier
     * @param {string} identifier - the identifier of the Script
     * @return {Script} the Script
     * @private
     */
    getScript(identifier) {
        return this.scripts[identifier];
    }

    /**
     * Get the Script associated with an identifier
     * @param {string} identifier - the identifier of the Script
     * @return {Script} the Script
     * @private
     */
    getCompiledScript() {
        return this.compileLogic(false);
    }

    /**
     * Get the identifiers of all registered scripts
     * @return {string[]} The identifiers of all registered scripts
     */
    getScriptIdentifiers() {
        return Object.keys(this.scripts);
    }

    /**
     * Compile the Ergo logic
     * @param {boolean} force - whether to force recompilation of the logic
     * @return {object} The script compiled to JavaScript
     */
    compileLogic(force) {
        if (this.compiledScript && !force) {
            return this.compiledScript;
        }
        let sourceErgo = this.getLogic();
        if (sourceErgo === undefined || sourceErgo.length === 0) {
            return null;
        }
        // Do not link to runtime for Java target, only for JavaScript
        const link = this.target === 'java' ? false : true;
        const compiledErgo = ErgoCompiler.compileToJavaScript(sourceErgo,this.modelManager.getModels(),this.target,link);
        if (compiledErgo.hasOwnProperty('error')) {
            throw new Error(ErgoCompiler.ergoVerboseErrorToString(compiledErgo.error));
        }
        const codeExt = this.target === 'java' ? '.java' : '.js';
        this.compiledScript = new Script(this.modelManager, 'main'+codeExt, codeExt, compiledErgo.success);
        return this.compiledScript;
    }

    /**
     * Helper method to retrieve all function declarations
     * @returns {Array} a list of function declarations
     */
    allFunctionDeclarations() {
        let allScripts = this.getAllScripts();
        const functionDeclarations = allScripts
            .map((ele) => {
                return ele.getFunctionDeclarations();
            }).reduce((flat, next) => {
                return flat.concat(next);
            },[]);
        return functionDeclarations;
    }

    /**
     * Looks for the presence of a function in the JavaScript logic
     * @param {string} name  - the function name
     */
    hasFunctionDeclaration(name) {
        // get the function declarations of either init or dispatch
        const funDecls = this.allFunctionDeclarations();
        if (!funDecls.some((ele) => { return ele.getName() === name; })) {
            throw new Error(`Function ${name} was not found in logic`);
        }
    }
    /**
     * Checks that the logic has a dispatch function
     */
    hasDispatch() {
        this.hasFunctionDeclaration('__dispatch');
    }

    /**
     * Checks that the logic has an init function
     */
    hasInit() {
        this.hasFunctionDeclaration('__init');
    }

}

module.exports = ScriptManager;
