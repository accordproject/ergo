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

const FileLoader = require('../lib/fileloader');

const chai = require('chai');
const except = chai.expect;

describe('FileLoader', () => {

    describe('#loadFileContents', () => {
        it('should return a Buffer if buffer is true', async () => {
            const content = await FileLoader.loadFileContents('packages/ergo-compiler/test/data', 'logo.png', false, false, true);
            except(content).to.be.instanceOf(Buffer);
        });
    });

});
