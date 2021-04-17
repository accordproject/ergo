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

const slash = require('slash');
const fsPath = require('path');

const ModelManager = require('@accordproject/concerto-core').ModelManager;
const ModelFile = require('@accordproject/concerto-core').ModelFile;
const Builtin = require('./builtin');

/**
 * Accord Project Model Manager. Bootstraps the ModelManager with system files.
 * @class
 * @public
 * @abstract
 * @memberof module:ergo-compiler
 */
class APModelManager extends ModelManager {

    /**
     */
    constructor() {
        super();
        this.addModelFile(Builtin.TimeModel, '@org.accordproject.time.cto');
        this.addModelFile(Builtin.MoneyModel, '@org.accordproject.money.cto');
        this.addModelFile(Builtin.ContractModel, '@org.accordproject.contract.cto');
        this.addModelFile(Builtin.RuntimeModel, '@org.accordproject.runtime.cto');
        this.validateModelFiles();
        this.builtInNamespaces = this.getNamespaces();
    }

    /**
     * Gets all the CTO models
     * @return {Array<{name:string, content:string}>} the name and content of each CTO file
     */
    getModels() {
        const modelFiles = this.getModelFiles();
        let models = [];
        modelFiles.forEach(function (file) {
            let fileName;
            // ignore the system namespace when creating an archive
            if (file.isSystemModelFile()) {
                return;
            }
            if (file.fileName === 'UNKNOWN' || file.fileName === null || !file.fileName) {
                fileName = file.namespace + '.cto';
            } else {
                let fileIdentifier = file.fileName;
                fileName = fsPath.basename(fileIdentifier);
            }
            models.push({ 'name' : fileName, 'content' : file.definitions });
        });
        return models;
    }

    /**
     * Adds a model file (as a string) to the TemplateLogic.
     * @param {string} modelFileContent - The model file content as a string
     * @param {string} fileName - an optional file name to associate with the model file
     */
    addAPModelFile(modelFileContent, fileName) {
        const name = slash(fileName);
        const modelFile = new ModelFile(this, modelFileContent, name);
        if (!this.builtInNamespaces.includes(modelFile.getNamespace())) {
            this.addModelFile(modelFile,name,true);
        }
    }

    /**
     * Add a set of model files to the TemplateLogic
     * @param {string[]} modelFiles - An array of Composer files as
     * strings.
     * @param {string[]} [modelFileNames] - An optional array of file names to
     * associate with the model files
     */
    addAPModelFiles(modelFiles, modelFileNames) {
        modelFiles.map((modelFileContent, index) => {
            const modelFileName = slash(modelFileNames[index]);
            this.addAPModelFile(modelFileContent, modelFileName);
        });
        this.validateModelFiles();
    }

    /**
     * Update of a given model
     * @param {string} content - the model content
     * @param {string} name - the model name
     */
    updateModel(content, name) {
        const currentModels = this.getModelFiles();
        // Is this a new model?
        if (!currentModels.some(x => x.getName() === name)) {
            this.addModelFile(content, name);
        } else {
            const previousModelFile =
                  (currentModels.filter(x => x.getName() === name))[0];
            const previousContent = previousModelFile.getDefinitions();
            if (content !== previousContent) {
                const previousNamespace = previousModelFile.getNamespace();
                const newNamespace = new ModelFile(this, content, name).getNamespace();
                if (previousNamespace === newNamespace) {
                    this.updateModelFile(content, name, true);
                } else {
                    this.deleteModelFile(previousNamespace);
                    this.addModelFile(content, name, true);
                }
            }
        }
    }
}

module.exports = APModelManager;