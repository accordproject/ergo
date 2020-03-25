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
const Logger = require('@accordproject/concerto-core').Logger;
const promisify = require('util').promisify;
const readdir = fs.readdir ? promisify(fs.readdir) : undefined;
const stat = fs.stat ? promisify(fs.stat) : undefined;

const ENCODING = 'utf8';

/**
 * A utility class to load files from zip or directories
 * @class
 * @private
 * @abstract
 */
class FileLoader {
    /**
     * Loads a required file from the zip, displaying an error if missing
     * @internal
     * @param {*} zip the JSZip instance
     * @param {string} path the file path within the zip
     * @param {boolean} json if true the file is converted to a JS Object using JSON.parse
     * @param {boolean} required whether the file is required
     * @return {Promise<string>} a promise to the contents of the zip file or null if it does not exist and
     * required is false
     */
    static async loadZipFileContents(zip, path, json=false, required=false) {
        Logger.debug('loadZipFileContents', 'Loading ' + path);
        let zipFile = zip.file(path);
        if(!zipFile && required) {
            throw new Error(`Failed to find ${path} in archive file.`);
        }

        if(zipFile) {
            const content = await zipFile.async('string');

            if(json && content) {
                return JSON.parse(content);
            }
            else {
                return FileLoader.normalizeNLs(content);
            }
        }

        return null;
    }

    /**
     * Loads the contents of all files in the zip that match a regex
     * @internal
     * @param {*} zip the JSZip instance
     * @param {RegExp} regex the regex to use to match files
     * @return {Promise<object[]>} a promise to an array of objects with the name and contents of the zip files
     */
    static async loadZipFilesContents(zip, regex) {
        const results = [];
        let matchedFiles = zip.file(regex);

        // do not use forEach, because we need to call an async function!
        for(let n=0; n < matchedFiles.length; n++) {
            const file = matchedFiles[n];
            const result = {name: file.name};
            result.contents = await FileLoader.loadZipFileContents(zip, file.name, false, true);
            results.push(result);
        }

        return results;
    }

    /**
     * Loads a required buffer of a file from the zip, displaying an error if missing
     * @internal
     * @param {*} zip the JSZip instance
     * @param {string} path the file path within the zip
     * @param {boolean} required whether the file is required
     * @return {Promise<Buffer>} a promise to the Buffer of the zip file or null if it does not exist and
     * required is false
     */
    static async loadZipFileBuffer(zip, path, required=false) {
        Logger.debug('loadZipFileBuffer', 'Loading ' + path);
        let zipFile = zip.file(path);
        if(!zipFile && required) {
            throw new Error(`Failed to find ${path} in archive file.`);
        }

        else if(zipFile) {
            return zipFile.async('nodebuffer');
        }

        return null;
    }

    /**
     * Loads a required file from a directory, displaying an error if missing
     * @internal
     * @param {*} path the root path
     * @param {string} fileName the relative file name
     * @param {boolean} json if true the file is converted to a JS Object using JSON.parse
     * @param {boolean} required whether the file is required
     * @return {Promise<string>} a promise to the contents of the file or null if it does not exist and
     * required is false
     */
    static async loadFileContents(path, fileName, json=false, required=false) {

        Logger.debug('loadFileContents', 'Loading ' + fileName);
        const filePath = fsPath.resolve(path, fileName);

        if (fs.existsSync(filePath)) {
            const contents = fs.readFileSync(filePath, ENCODING);
            if(json && contents) {
                return JSON.parse(contents);
            }
            else {
                return FileLoader.normalizeNLs(contents);
            }
        }
        else {
            if(required) {
                throw new Error(`Failed to find ${fileName} in directory.`);
            }
        }

        return null;
    }

    /**
     * Loads a file as buffer from a directory, displaying an error if missing
     * @internal
     * @param {*} path the root path
     * @param {string} fileName the relative file name
     * @param {boolean} required whether the file is required
     * @return {Promise<Buffer>} a promise to the buffer of the file or null if
     * it does not exist and required is false
     */
    static async loadFileBuffer(path, fileName, required=false) {

        Logger.debug('loadFileBuffer', 'Loading ' + fileName);
        const filePath = fsPath.resolve(path, fileName);

        if (fs.existsSync(filePath)) {
            return fs.readFileSync(filePath);
        }
        else {
            if(required) {
                throw new Error(`Failed to find ${fileName} in directory`);
            }
        }
        return null;
    }

    /**
     * Loads the contents of all files under a path that match a regex
     * Note that any directories called node_modules are ignored.
     * @internal
     * @param {*} path the file path
     * @param {RegExp} regex the regex to match files
     * @return {Promise<object[]>} a promise to an array of objects with the name and contents of the files
     */
    static async loadFilesContents(path, regex) {

        Logger.debug('loadFilesContents', 'Loading ' + path);
        const subdirs = await readdir(path);
        const result = await Promise.all(subdirs.map(async (subdir) => {
            const res = fsPath.resolve(path, subdir);

            if((await stat(res)).isDirectory()) {
                if( /.*node_modules$/.test(res) === false) {
                    return FileLoader.loadFilesContents(res, regex);
                }
                else {
                    return null;
                }
            }
            else {
                if(regex.test(res)) {
                    return {
                        name: res,
                        contents: await FileLoader.loadFileContents(path, res, false, true)
                    };
                }
                else {
                    return null;
                }
            }
        }));
        return result.reduce((a, f) => a.concat(f), []).filter((f) => f !== null);
    }

    /**
     * Prepare the text for parsing (normalizes new lines, etc)
     * @param {string} input - the text for the clause
     * @return {string} - the normalized text for the clause
     */
    static normalizeNLs(input) {
        // we replace all \r and \n with \n
        let text =  input.replace(/\r/gm,'');
        return text;
    }

}

module.exports = FileLoader;