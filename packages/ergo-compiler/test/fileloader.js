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
const JSZip = require('jszip');
const chai = require('chai');
const expect = chai.expect;

const FileLoader = require('../lib/fileloader');

describe('FileLoader', () => {

    describe('#loadFileBuffer', () => {
        it('should return an instace of Buffer', async () => {
            const content = await FileLoader.loadFileBuffer('./test/data', 'logo.png', true);
            expect(content).to.be.instanceOf(Buffer);
        });

        it('should return null if file is not found and required is false', async () => {
            const content = await FileLoader.loadFileBuffer('./test', 'logo.png', false);
            expect(content).to.be.null;
        });

        it('should throw an error if file is not found and required is true', async () => {
            await expect(FileLoader.loadFileBuffer('./test', 'logo.png', true)).to.be.eventually.rejectedWith(Error);
        });
    });

    describe('#loadZipFileBuffer', () => {
        it('should return an instance of Buffer', () => {
            const zip = new JSZip();
            zip.loadAsync(fs.readFileSync('./test/data/logo.zip'))
                .then(async (zip) => {
                    const content = await FileLoader.loadZipFileBuffer(zip, 'logo.png', true);
                    expect(content).to.be.an.instanceOf(Buffer);
                });
        });

        it('should return null if path is not found inside the zip and required is false', async () => {
            const zip = new JSZip();
            const content = await FileLoader.loadZipFileBuffer(zip, 'logo.png', false);
            expect(content).to.be.null;
        });

        it('should throw an error if path is not found inside the zip and required is true', async () => {
            const zip = new JSZip();
            await expect(FileLoader.loadZipFileBuffer(zip, 'logo.png', true)).to.be.eventually.rejectedWith(Error);
        });
    });

    describe('#loadZipFileContents', () => {
        it('should return an instance of file', () => {
            const zip = new JSZip();
            zip.loadAsync(fs.readFileSync('../../tests/helloworldcontract.zip'))
                .then(async (zip) => {
                    expect(
                        await FileLoader.loadZipFileContents(zip, 'helloworldcontract/request.json', true, false)
                    ).to.deep.equal({
                        '$class': 'org.accordproject.helloworld.Request',
                        'input': 'Accord Project',
                    });
                });
        });

        it('should return null if path is not found inside the zip and required is false', async () => {
            const zip = new JSZip();
            const content = await FileLoader.loadZipFileContents(zip, 'requiest.json', true, false);
            expect(content).to.be.null;
        });

        it('should throw an error if path is not found inside the zip and required is true', async () => {
            const zip = new JSZip();
            await expect(FileLoader.loadZipFileContents(zip, 'request.json', true, true)).to.be.eventually.rejectedWith(Error);
        });
    });

    describe('#loadFileContents', () => {
        it('should return an instance of file', async () => {
            const content = await FileLoader.loadFileContents('../../tests/helloworldcontract', 'request.json', true, false);
            expect(content).to.deep.equal({
                '$class': 'org.accordproject.helloworld.Request',
                'input': 'Accord Project',
            });
        });

        it('should return null if path is not found and required is false', async () => {
            const content = await FileLoader.loadFileContents('../../tests/helloworldcontract', 'foo.json', true, false);
            expect(content).to.be.null;
        });

        it('should throw an error if path is not found and required is true', async () => {
            await expect(FileLoader.loadFileContents('../../tests/helloworldcontract', 'foo.json', true, true)).to.be.eventually.rejectedWith(Error);
        });
    });

});
