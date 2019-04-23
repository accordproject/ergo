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
const ResourceValidator = require('composer-concerto/lib/serializer/resourcevalidator');
const ModelFile = require('composer-concerto').ModelFile;
const APModelManager = require('../lib/apmodelmanager');
const ScriptManager = require('../lib/scriptmanager');
const ErgoCompiler = require('./compiler');
const Builtin = require('./builtin');

/**
 * Packages the logic for a legal clause or contract template and a given target platform. This includes the model, Ergo logic and compiled version of that logic when required.
 * @class
 * @public
 * @abstract
 * @memberof module:ergo-compiler
 */
class LogicManager {

    /**
     * Create the LogicManager.
     * @param {String} target  - compiler target (either: 'cicero', 'es5', 'es6', or 'java')
     * @param {string} sourceTemplate - an optional template source
     * @param {Object} options  - e.g., { warnings: true }
     */
    constructor(target, sourceTemplate, options) {
        ErgoCompiler.isValidTarget(target);
        this.target = target;
        this.contractName = null;
        this.modelManager = new APModelManager();
        this.scriptManager = new ScriptManager(this.target, this.modelManager, sourceTemplate, options);
        this.introspector = new Introspector(this.modelManager);
        this.factory = new Factory(this.modelManager);
        this.serializer = new Serializer(this.factory, this.modelManager);
        this.validated = false;
        this.addModelFile(Builtin.markdownModel, 'org.accordproject.markdown');
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
        this.contractName = ErgoCompiler.contractCallName(contractName);
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
const __result = __dispatch({contract:context.data,state:context.state,emit:[],now:context.now,request:context.request});
unwrapError(__result);
        `;
        } else if (target === 'es6') {
            if (this.getContractName()) {
                const contractName = this.getContractName();
                code = `
let contractObj = new ${contractName}();
const __result = contractObj.main({contract:context.data,state:context.state,emit:[],now:context.now,request:context.request});
unwrapError(__result);
`;
            } else {
                throw new Error(`Cannot create dispatch call for target: ${target} without a contract name`);
            }
        } else if (target === 'es5') {
            code = `
const __result = main({contract:context.data,state:context.state,emit:[],now:context.now,request:context.request});
unwrapError(__result);
`;
        } else {
            throw new Error(`Unsupported target: ${target}`);
        }
        return code;
    }

    /**
     * Generate the invocation logic
     * @param {String} clauseName - the clause name
     * @return {String} the invocation code
     * @private
     */
    getInvokeCall(clauseName) {
        const target = this.getTarget();
        let code;
        if (target === 'cicero' || target === 'es6') {
            if (this.getContractName()) {
                const contractName = this.getContractName();
                code = `
let contractObj = new ${contractName}();
const __result = contractObj.${clauseName}(Object.assign({}, {contract:context.data,state:context.state,emit:[],now:context.now} ,context.params));
unwrapError(__result);
`;
            } else {
                throw new Error(`Cannot create invoke call for target: ${target} without a contract name`);
            }
        } else if (target === 'es5') {
            code = `
const __result = ${clauseName}(Object.assign({}, {contract:context.data,state:context.state,emit:[],now:context.now} ,context.params));
unwrapError(__result);
`;
        } else {
            throw new Error(`Unsupported target: ${target}`);
        }
        return code;
    }

    /**
     * Provides access to the Introspector for this TemplateLogic. The Introspector
     * is used to reflect on the types defined within this TemplateLogic.
     * @return {Introspector} the Introspector for this TemplateLogic
     */
    getIntrospector() {
        return this.introspector;
    }

    /**
     * Provides access to the Factory for this TemplateLogic. The Factory
     * is used to create the types defined in this TemplateLogic.
     * @return {Factory} the Factory for this TemplateLogic
     */
    getFactory() {
        return this.factory;
    }

    /**
     * Provides access to the Serializer for this TemplateLogic. The Serializer
     * is used to serialize instances of the types defined within this TemplateLogic.
     * @return {Serializer} the Serializer for this TemplateLogic
     */
    getSerializer() {
        return this.serializer;
    }

    /**
     * Provides access to the ScriptManager for this TemplateLogic. The ScriptManager
     * manage access to the scripts that have been defined within this TemplateLogic.
     * @return {ScriptManager} the ScriptManager for this TemplateLogic
     */
    getScriptManager() {
        return this.scriptManager;
    }

    /**
     * Provides access to the ModelManager for this TemplateLogic. The ModelManager
     * manage access to the models that have been defined within this TemplateLogic.
     * @return {ModelManager} the ModelManager for this TemplateLogic
     */
    getModelManager() {
        return this.modelManager;
    }

    /**
     * Adds a logic file (as a string) to the TemplateLogic.
     * @param {string} logicFile - The logic file as a string
     * @param {string} fileName - an optional file name to associate with the logic file
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
     * Adds a template file (as a string) to the TemplateLogic.
     * @param {string} templateFile - The template file as a string
     * @param {string} fileName - an optional file name to associate with the template file
     */
    addTemplateFile(templateFile,fileName) {
        this.getScriptManager().addTemplateFile(templateFile,fileName);
    }

    /**
     * Adds a model file (as a string) to the TemplateLogic.
     * @param {string} modelFile - The model file as a string
     * @param {string} fileName - an optional file name to associate with the model file
     */
    addModelFile(modelFile, fileName) {
        this.validated = false;
        this.getModelManager().addModelFile(modelFile,fileName,true);
    }

    /**
     * Add a set of model files to the TemplateLogic
     * @param {string[]} modelFiles - An array of Composer files as
     * strings.
     * @param {string[]} [modelFileNames] - An optional array of file names to
     * associate with the model files
     */
    addModelFiles(modelFiles, modelFileNames) {
        this.validated = false;
        this.getModelManager().addModelFiles(modelFiles, modelFileNames, true);
    }

    /**
     * Validate model files
     */
    validateModelFiles() {
        if (!this.validated) {
            this.getModelManager().validateModelFiles();
            this.validated = true;
        }
    }

    /**
     * Compiles the logic to the target.
     * @param {boolean} force - whether to force recompilation of the logic
     * @return {object} The script compiled to JavaScript
     */
    compileLogicSync(force) {
        this.validateModelFiles();
        const script = this.getScriptManager().compileLogic(force);
        if (script && script.getContractName()) {
            this.setContractName(script.getContractName());
        }
        return script;
    }

    /**
     * Compiles the logic to the target.
     * @param {boolean} force - whether to force recompilation of the logic
     * @return {object} A promise to the script compiled to JavaScript
     */
    compileLogic(force) {
        try {
            this.compileLogicSync(force);
            return Promise.resolve(undefined);
        } catch (error) {
            return Promise.reject(error);
        }
    }

    /**
     * Add Ergo built-in models
     */
    addErgoBuiltin() {
        this.addModelFile(Builtin.timeModel, 'org.accordproject.time');
        this.addModelFile(Builtin.moneyModel, 'org.accordproject.money');
        this.addModelFile(Builtin.contractModel, 'org.accordproject.cicero.contract');
        this.addModelFile(Builtin.runtimeModel, 'org.accordproject.cicero.runtime');
        this.validateModelFiles();
    }

    /**
     * Validate input JSON
     * @param {object} input - the input JSON
     * @return {object} the validated input
     */
    validateInput(input) {
        const serializer = this.getSerializer();

        if (input === null) { return null; }

        // ensure the input is valid
        const validInput = serializer.fromJSON(input, {validate: false, acceptResourcesForRelationships: true});
        validInput.$validator = new ResourceValidator({permitResourcesForRelationships: true});
        validInput.validate();
        return serializer.toJSON(validInput, {permitResourcesForRelationships:true});
    }

    /**
     * Validate input JSON record
     * @param {object} input - the input JSON record
     * @return {object} the validated input
     */
    validateInputRecord(input) {
        let validRecord = {};
        for(const key in input) {
            if (input[key] instanceof Object) {
                validRecord[key] = this.validateInput(input[key]);
            } else {
                validRecord[key] = input[key];
            }
        }
        return validRecord;
    }

    /**
     * Validate output JSON
     * @param {object} output - the output JSON
     * @return {object} the validated output
     */
    validateOutput(output) {
        const serializer = this.getSerializer();

        if (output === null) { return null; }

        if (output instanceof Object) {
            const validOutput = serializer.fromJSON(output, {validate: false, acceptResourcesForRelationships: true});
            validOutput.$validator = new ResourceValidator({permitResourcesForRelationships: true});
            validOutput.validate();
            return serializer.toJSON(validOutput, {convertResourcesToRelationships: true});
        } else {
            return output;
        }
    }

    /**
     * Validate output JSON array
     * @param {Array<object>} outputArray - the output JSON array
     * @return {Array<object>} the validated output array
     */
    validateOutputArray(outputArray) {
        let resultArray = [];
        for (let i = 0; i < outputArray.length; i++) {
            resultArray.push(this.validateOutput(outputArray[i]));
        }
        return resultArray;
    }

    /**
     * Update of a given model
     * @param {string} content - the model content
     * @param {string} name - the model name
     */
    updateModel(content, name) {
        const modelManager = this.getModelManager();
        const currentModels = modelManager.getModelFiles();
        // Is this a new model?
        if (!currentModels.some(x => x.getName() === name)) {
            modelManager.addModelFile(content, name);
        } else {
            const previousModelFile =
                  (currentModels.filter(x => x.getName() === name))[0];
            const previousContent = previousModelFile.getDefinitions();
            if (content !== previousContent) {
                modelManager.validateModelFile(content, name);
                const previousNamespace = previousModelFile.getNamespace();
                const newNamespace = new ModelFile(modelManager, content, name).getNamespace();
                if (previousNamespace === newNamespace) {
                    modelManager.updateModelFile(content, name, true);
                } else {
                    modelManager.deleteModelFile(previousNamespace);
                    modelManager.addModelFile(content, name, true);
                }
            }
        }
    }

    /**
     * Update of a given logic file
     * @param {string} content - the logic content
     * @param {string} name - the logic name
     */
    updateLogic(content, name) {
        const scriptManager = this.getScriptManager();
        if (!scriptManager.getScript(name)) {
            this.addLogicFile(content,name);
        } else {
            if (scriptManager.getScript(name).getContents() !== content) {
                scriptManager.modifyScript(name, '.ergo', content);
            }
        }
    }

}

module.exports = LogicManager;