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

const fsPath = require('path');

const ModelManager = require('composer-concerto').ModelManager;
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
        this.addModelFile(Builtin.systemModel, 'org.accordproject.base.cto', false, true);
        this.addModelFile(Builtin.markdownModel, '@org.accordproject.markdown', false, true);
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

}

module.exports = APModelManager;