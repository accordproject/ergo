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
 * <p>
 * Ergo Error class.
 * </p>
 * @class
 * @public
 * @memberof module:ergo-compiler
 */
class ErgoError extends Error {
    /**
     * Parse CTO to JSON
     *
     * @param {object} descriptor - JSON Ergo error descriptor
     */
    constructor(descriptor) {
        super(descriptor.verbose);
        this.descriptor = descriptor;
    }
}

module.exports = ErgoError;
