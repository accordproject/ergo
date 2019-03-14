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

const Factory = require('composer-concerto').Factory;
const Introspector = require('composer-concerto').Introspector;
const Serializer = require('composer-concerto').Serializer;
const APModelManager = require('../lib/apmodelmanager');
const ScriptManager = require('../lib/scriptmanager');
const ErgoCompiler = require('./compiler');

/**
 * Packages the logic for a legal clause or contract template and a given target platform. This includes the model, Ergo logic and compiled version of that logic when required.
 * @class
 * @public
 * @abstract
 * @memberof module:ergo-compiler
 */
class TemplateLogic {

    /**
     * Create the TemplateLogic.
     * @param {String} target  - compiler target (either: 'cicero', 'es5', 'es6', or 'java')
     */
    constructor(target) {
        this.target = target;
        this.contractName = null;
        this.modelManager = new APModelManager();
        this.scriptManager = new ScriptManager(this.target, this.modelManager);
        this.introspector = new Introspector(this.modelManager);
        this.factory = new Factory(this.modelManager);
        this.serializer = new Serializer(this.factory, this.modelManager);
    }

    /**
     * Get the compilation target.
     * @return {String} the compiler target (either: 'cicero', 'es5', 'es6', or 'java')
     */
    getTarget() {
        return this.target;
    }

    /**
     * Set the compilation target. Note: This might force recompilation if logic has already been compiled.
     * @param {String} target - compiler target (either: 'cicero', 'es5', 'es6', or 'java')
     * @param {boolean} recompile - whether to force recompilation of the logic
     */
    setTarget(target, recompile) {
        this.target = target;
        this.getScriptManager().changeTarget(target, recompile);
    }

    /**
     * Set the contract name
     * @param {String} contractName - the contract name
     */
    setContractName(contractName) {
        this.contractName = contractName;
    }

    /**
     * Get the contract name
     * @return {String} the contract name
     */
    getContractName() {
        return this.contractName;
    }

    /**
     * Generate the runtime dispatch logic
     * @return {String} the dispatch code
     * @private
     */
    getDispatchCall() {
        const target = this.getTarget();
        let code;
        if (target === 'cicero') {
            this.getScriptManager().hasDispatch();
            code = `
__dispatch({contract:data,request:request,state:state,now:now,emit:[]});
        `;
        } else if (target === 'es6') {
            if (this.getContractName()) {
                const contractName = ErgoCompiler.contractCallName(this.getContractName());
                code = `
let contract = new ${contractName}();
contract.main({contract:data,request:request,state:state,now:now,emit:[]});
`;
            } else {
                throw new Error(`Cannot create dispatch call for target: ${target} without a contract name`);
            }
        } else if (target === 'es5') {
            code = `
main({contract:data,request:request,state:state,now:now,emit:[]});
`;
        } else {
            throw new Error(`Unsupported target: ${target}`);
        }
        return code;
    }

    /**
     * Generate the initialization logic
     * @return {String} the initialization code
     * @private
     */
    getInitCall() {
        const target = this.getTarget();
        let code;
        if (target === 'cicero') {
            this.getScriptManager().hasDispatch();
            code = `
__init({contract:data,request:null,now:now,emit:[]});
        `;
        } else if (target === 'es6') {
            if (this.getContractName()) {
                const contractName = ErgoCompiler.contractCallName(this.getContractName());
                code = `
let contract = new ${contractName}();
contract.init({contract:data,request:null,now:now,emit:[]});
`;
            } else {
                throw new Error(`Cannot create init call for target: ${target} without a contract name`);
            }
        } else if (target === 'es5') {
            code = `
init({contract:data,request:null,now:now,emit:[]});
`;
        } else {
            throw new Error(`Unsupported target: ${target}`);
        }
        return code;
    }

    /**
     * Provides access to the Introspector for this Template Logic. The Introspector
     * is used to reflect on the types defined within this Template Logic.
     * @return {Introspector} the Introspector for this Template Logic
     */
    getIntrospector() {
        return this.introspector;
    }

    /**
     * Provides access to the Factory for this Template Logic. The Factory
     * is used to create the types defined in this Template Logic.
     * @return {Factory} the Factory for this Template Logic
     */
    getFactory() {
        return this.factory;
    }

    /**
     * Provides access to the Serializer for this Template Logic. The Serializer
     * is used to serialize instances of the types defined within this Template Logic.
     * @return {Serializer} the Serializer for this Template Logic
     */
    getSerializer() {
        return this.serializer;
    }

    /**
     * Provides access to the ScriptManager for this Template Logic. The ScriptManager
     * manage access to the scripts that have been defined within this Template Logic.
     * @return {ScriptManager} the ScriptManager for this Template Logic
     */
    getScriptManager() {
        return this.scriptManager;
    }

    /**
     * Provides access to the ModelManager for this Template Logic. The ModelManager
     * manage access to the models that have been defined within this Template Logic.
     * @return {ModelManager} the ModelManager for this Template Logic
     */
    getModelManager() {
        return this.modelManager;
    }

    /**
     * Adds a model file (as a string) to the Template Logic.
     * @param {string} modelFile - The model file as a string
     * @param {string} fileName - an optional file name to associate with the model file
     */
    addModelFile(modelFile, fileName) {
        this.getModelManager().addModelFile(modelFile,fileName,true);
    }

    /**
     * Adds a logic file (as a string) to the Template Logic.
     * @param {string} logicFile - The logic file as a string
     * @param {string} fileName - an optional file name to associate with the model file
     */
    addLogicFile(logicFile,fileName) {
        const logicFileName = fileName;
        let logicExt;
        if (fileName.indexOf('.') === -1) {
            logicExt = '.ergo';
        } else {
            logicExt = '.' +  fileName.split('.').pop();
        }
        let scriptObject = this.getScriptManager().createScript(logicFileName, logicExt, logicFile);
        this.getScriptManager().addScript(scriptObject);
    }

    /**
     * Add a set of model files to the Template Logic
     * @param {string[]} modelFiles - An array of Composer files as
     * strings.
     * @param {string[]} [modelFileNames] - An optional array of file names to
     * associate with the model files
     */
    addModelFiles(modelFiles, modelFileNames) {
        this.getModelManager().addModelFiles(modelFiles, modelFileNames, true);
    }

    /**
     * Compiles the logic to the target.
     * @param {boolean} force - whether to force recompilation of the logic
     */
    compileLogic(force) {
        this.getScriptManager().compileLogic(force);
    }

}

module.exports = TemplateLogic;