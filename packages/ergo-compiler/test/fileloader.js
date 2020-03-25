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
const expect = chai.expect;

describe('FileLoader', () => {

    describe('#loadFileBuffer', () => {

        it('should return an instace of Buffer if required is true', async () => {
            const content = await FileLoader.loadFileBuffer('./test/data', 'logo.png', true);
            expect(content).to.be.instanceOf(Buffer);
        });

        it('should return null if file is not found and required is false', async () => {
            const content = await FileLoader.loadFileBuffer('./test', 'logo.png', false);
            expect(content).to.be.null;
        });

        it('should throw an error if the mime-type is not allowed', async () => {
            await expect(FileLoader.loadFileBuffer('./test/data/fakePNG', 'logo.png', true)).to.be.eventually.rejectedWith(Error);
        });

        it('should throw an error if the image is of incorrect aspectRatio', async () => {
            await expect(FileLoader.loadFileBuffer('./test/data', 'logo.png', true, 2, 0.05)).to.be.eventually.rejectedWith(Error);
        });
    });

});
