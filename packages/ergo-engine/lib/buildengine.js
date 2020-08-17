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

const WasmEngine = require('./wasmengine');
const EvalEngine = require('./evalengine');
const VMEngine = require('./vmengine');

/**
 * @param {string} target - the target runtime
 * @param {boolean} browser - run in the browser
 * @return {*} an execution engine
 */
function buildEngine(target,browser) {
    if (target === 'wasm') {
        return new WasmEngine();
    } else if (browser) {
        return new EvalEngine();
    } else {
        return new VMEngine();
    }
}

module.exports = buildEngine;
