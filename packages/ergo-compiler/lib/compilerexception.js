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

const BaseFileException = require('@accordproject/concerto').BaseFileException;

/**
 * Exception throws when ergo compilation fails
 * @extends BaseFileException
 * @see See  {@link BaseFileException}
 * @class
 * @memberof module:ergo-compiler
 * @private
 */
class CompilerException extends BaseFileException {
    /**
     * Create a CompilerException
     * @param {String} message - the message for the exception
     * @param {Object} [fileLocation] - location details of the error within the model file.
     * @param {number} fileLocation.start.line - start line of the error location.
     * @param {number} fileLocation.start.column - start column of the error location.
     * @param {number} fileLocation.end.line - end line of the error location.
     * @param {number} fileLocation.end.column - end column of the error location.
     * @param {String} fullMessage - the optional full message text
     * @param {String} [fileName] - the optional fileName associated with the exception
     * @param {String} component - the optional component which throws this error
     */
    constructor(message, fileLocation, fullMessage, fileName, component) {
        super(message, fileLocation, fullMessage, fileName, component || 'ergo-compiler');
    }
}

module.exports = CompilerException;
