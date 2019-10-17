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

const Chai = require('chai');
const expect = Chai.expect;

/**
 * Resolve the root directory
 *
 * @param {string} parameters Cucumber's World parameters
 * @return {string} root directory used to resolve file names
 */
function resolveRootDir(parameters) {
    if (parameters.rootdir) {
        return parameters.rootdir;
    } else {
        return '.';
    }
}

/**
 * Compare actual and expected result components
 *
 * @param {string} expected the expected component as specified in the test workload
 * @param {string} actual the actual component as returned by the engine
 */
function compareComponent(expected,actual) {
    if (!expected) {
        expect(actual).to.equal(expected);
    } else {
        delete expected.timestamp;
        delete actual.timestamp;
        // Some basic deep comparison for arrays, since Chai doesn't do the right thing
        if (Array.isArray(actual)) {
            for (let i = 0; i < expected.length; i++) {
                delete expected[i].timestamp;
                delete actual[i].timestamp;
                expect(actual[i]).to.deep.include(expected[i]);
            }
        } else {
            expect(actual).to.deep.include(expected);
        }
    }
}

/**
 * Compare actual result and expected result
 *
 * @param {string} expected the expected successful result as specified in the test workload
 * @param {string} actual the successful result as returned by the engine
 */
function compareSuccess(expected,actual) {
    if (Object.prototype.hasOwnProperty.call(expected, 'state')) {
        expect(actual).to.have.property('state');
        compareComponent(expected.state, actual.state);
    }
    if (Object.prototype.hasOwnProperty.call(expected, 'response')) {
        expect(actual).to.have.property('response');
        compareComponent(expected.response, actual.response);
    }
    if (Object.prototype.hasOwnProperty.call(expected, 'emit')) {
        expect(actual).to.have.property('emit');
        compareComponent(expected.emit, actual.emit);
    }
}

module.exports = { resolveRootDir, compareComponent, compareSuccess };
