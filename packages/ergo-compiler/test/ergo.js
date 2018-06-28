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

const Ergo = require('../lib/ergo');
const Chai = require('chai');

Chai.should();
Chai.use(require('chai-things'));

const Fs = require('fs');
const Path = require('path');

describe('ergo-compiler', () => {

    afterEach(() => {});

    describe('#callname', function () {
        it('should sanitize call names for contracts', async function () {
            const contractName = 'org.accordproject.volumediscount.VolumeDiscount';
            const result = await Ergo.contractCallNamePromise(contractName);
            result.should.equal('orgXaccordprojectXvolumediscountXVolumeDiscount');
        });
    });

    describe('#parsefail', function () {
        it('should fail when Ergo does not parse', async function () {
            const ergoText = Fs.readFileSync(Path.resolve(__dirname, 'data/bad-logic', 'logic.ergo'), 'utf8');
            const ctoText = Fs.readFileSync(Path.resolve(__dirname, 'data/bad-logic', 'model.cto'), 'utf8');
            const result = await Ergo.compile(ergoText, [ctoText], 'javascript');
            result.should.deep.equal({ 'error' : { 'kind' : 'ParseError', 'message' : 'Parse error', 'locstart' : { 'line' : 17, 'character' : 20 }, 'locend' : { 'line' : 17, 'character' : 23 } } });
        });
    });
    describe('#parseerrormessage', function () {
        it('should format parse error', async function () {
            const result = await Ergo.ergoErrorToString({ 'kind' : 'ParseError', 'message' : 'Parse error', 'locstart' : { 'line' : 16, 'character' : 25 }, 'locend' : { 'line' : 16, 'character' : 26 } });
            result.should.deep.equal('Parse error at line 16 character 25');
        });
    });
    describe('#compilationerrormessage', function () {
        it('should format compilation error', async function () {
            const result = await Ergo.ergoErrorToString({ 'kind' : 'CompilationError', 'message' : 'Import not found: org.accordproject.base', 'locstart' : { 'line' : -1, 'character' : -1 }, 'locend' : { 'line' : -1, 'character' : -1 } });
            result.should.deep.equal('Import not found: org.accordproject.base');
        });
    });
    describe('#compilehellojs', function () {
        it('should compile a smart Ergo contract to JavaScript', async function () {
            const ergoText = Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'logic.ergo'), 'utf8');
            const ctoText = Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'model.cto'), 'utf8');
            const result = await Ergo.compile(ergoText, [ctoText], 'javascript');
            result.success.should.not.be.null;
        });
    });
    describe('#compileandlinkhellojs', function () {
        it('should compile and link a smart Ergo contract to JavaScript', async function () {
            const ergoText = Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'logic.ergo'), 'utf8');
            const ctoText = Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'model.cto'), 'utf8');
            const result = await Ergo.compileAndLink(ergoText, [ctoText], 'javascript');
            result.success.should.not.be.null;
        });
    });
    describe('#compilehellocicero', function () {
        it('should compile a smart Ergo contract to JavaScript for Cicero', async function () {
            const ergoText = Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'logic.ergo'), 'utf8');
            const ctoText = Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'model.cto'), 'utf8');
            const result = await Ergo.compile(ergoText, [ctoText], 'javascript_cicero');
            result.success.should.not.be.null;
        });
    });
    describe('#compilelatedeliveryfail', function () {
        it('should fail when compiling a smart Ergo contract to JavaScript', async function () {
            const ergoText = Fs.readFileSync(Path.resolve(__dirname, 'data/latedeliveryandpenalty', 'logic.ergo'), 'utf8');
            const ctoText = Fs.readFileSync(Path.resolve(__dirname, 'data/latedeliveryandpenalty', 'model.cto'), 'utf8');
            const result = await Ergo.compile(ergoText, [ctoText], 'javascript');
            result.should.deep.equal({ 'error' : { 'kind' : 'CompilationError', 'message' : 'Import not found: org.accordproject.base', 'locstart' : { 'line' : -1, 'character' : -1 }, 'locend' : { 'line' : -1, 'character' : -1 } } });
        });
    });
    describe('#compilelatedeliveryandlinkfail', function () {
        it('should fail when compiling and linking a smart Ergo contract to JavaScript', async function () {
            const ergoText = Fs.readFileSync(Path.resolve(__dirname, 'data/latedeliveryandpenalty', 'logic.ergo'), 'utf8');
            const ctoText = Fs.readFileSync(Path.resolve(__dirname, 'data/latedeliveryandpenalty', 'model.cto'), 'utf8');
            const result = await Ergo.compileAndLink(ergoText, [ctoText], 'javascript');
            result.should.deep.equal({ 'error' : { 'kind' : 'CompilationError', 'message' : 'Import not found: org.accordproject.base', 'locstart' : { 'line' : -1, 'character' : -1 }, 'locend' : { 'line' : -1, 'character' : -1 } } });
        });
    });
    describe('#parsecto', function () {
        it('should parse CTO', async function () {
            const ctoText = Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'model.cto'), 'utf8');
            const result = await Ergo.parseCTO(ctoText);
            result.should.not.be.null;
        });
    });
    describe('#commonctos', function () {
        it('should return built-in CTOs', async function () {
            const result = Ergo.commonCTOs();
            result.should.have.lengthOf(4);
        });
    });
});
