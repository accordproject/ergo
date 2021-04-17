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

const fs = require('fs');
const fsPath = require('path');
const slash = require('slash');
const JSZip = require('jszip');

const FileLoader = require('./fileloader');
const LogicManager = require('./logicmanager');

/**
 * Builds a LogicManager from a directory.
 *
 * @param {String} path to a local directory
 * @param {Object} [options] - an optional set of options to configure the instance.
 * @return {Promise<LogicManager>} a Promise to the instantiated logicmanager
 */
async function fromDirectory(path, options) {
    if (!options) {
        options = {};
    }

    const logicManager = new LogicManager('es6', options);

    const ctoFiles = await FileLoader.loadFilesContents(path, /model[/\\].*\.cto$/);
    ctoFiles.forEach((file) => {
        logicManager.getModelManager().addAPModelFile(file.contents, file.name);
    });

    // Update external models
    await logicManager.getModelManager().updateExternalModels();

    // load and add the ergo files
    const ergoFiles = await FileLoader.loadFilesContents(path, /logic[/\\].*\.ergo$/);
    ergoFiles.forEach((file) => {
        const resolvedPath = slash(fsPath.resolve(path));
        const resolvedFilePath = slash(fsPath.resolve(file.name));
        const truncatedPath = resolvedFilePath.replace(resolvedPath+'/', '');
        logicManager.addLogicFile(file.contents, truncatedPath);
    });

    // load and add the formulas
    let formulas = await FileLoader.loadFilesContents(path, /text[/\\].*\.tem$/);
    formulas.forEach((file) => {
        const baseName = fsPath.basename(file.name).replace('.tem','');
        logicManager.addTemplateFile(file.contents, baseName);
    });

    return logicManager;
}

/**
 * Builds a LogicManager from a Zip.
 *
 * @param {Buffer} buffer - the buffer to a Zip (zip) file
 * @param {Object} [options] - an optional set of options to configure the instance.
 * @return {Promise<LogicManager>} a Promise to the instantiated logicmanager
 */
async function fromZip(buffer, options) {
    if (!options) {
        options = {};
    }

    const zip = await JSZip.loadAsync(buffer);
    const logicManager = new LogicManager('es6', options);

    const ctoFiles = await FileLoader.loadZipFilesContents(zip, /model[/\\].*\.cto$/);
    ctoFiles.forEach((file) => {
        logicManager.getModelManager().addAPModelFile(file.contents, file.name);
    });

    // Update external models
    await logicManager.getModelManager().updateExternalModels();

    // load and add the ergo files
    const ergoFiles = await FileLoader.loadZipFilesContents(zip, /logic[/\\].*\.ergo$/);
    ergoFiles.forEach((file) => {
        logicManager.addLogicFile(file.contents, file.name);
    });

    // load and add the formulas
    let formulas = await FileLoader.loadZipFilesContents(zip, /text[/\\].*\.tem$/);
    formulas.forEach((file) => {
        const baseName = fsPath.basename(file.name).replace('.tem','');
        logicManager.addTemplateFile(file.contents, baseName);
    });

    return logicManager;
}

/**
 * Builds a LogicManager from files.
 *
 * @param {String[]} files - file names
 * @param {Object} [options] - an optional set of options to configure the instance.
 * @return {Promise<LogicManager>} a Promise to the instantiated logicmanager
 */
async function fromFiles(files, options) {
    if (!options) {
        options = {};
    }

    const logicManager = new LogicManager('es6', options);

    let modelPaths = [];
    let logicPaths = [];
    let formulaPaths = [];

    for (let i = 0; i < files.length; i++) {
        const file = files[i];
        if (file.split('.').pop() === 'cto') {
            modelPaths.push(file);
        } else if (file.split('.').pop() === 'ergo') {
            logicPaths.push(file);
        } else if (file.split('.').pop() === 'tem') {
            formulaPaths.push(file);
        }
    }
    modelPaths.forEach((path) => {
        const file = fs.readFileSync(path, 'utf8');
        logicManager.getModelManager().addAPModelFile(file, path);
    });

    // Update external models
    await logicManager.getModelManager().updateExternalModels();

    // load and add the ergo files
    logicPaths.forEach((path) => {
        const file = fs.readFileSync(path, 'utf8');
        logicManager.addLogicFile(file, path);
    });

    // load and add the formulas
    formulaPaths.forEach((path) => {
        const file = fs.readFileSync(path, 'utf8');
        const baseName = fsPath.basename(path).replace('.tem','');
        logicManager.addTemplateFile(file, baseName);
    });

    return logicManager;
}

module.exports = { fromDirectory, fromZip, fromFiles };
