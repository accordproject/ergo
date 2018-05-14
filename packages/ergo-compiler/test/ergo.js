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

    describe('#compilehellojs', function () {
        it('should compile a smart Ergo contract to JavaScript', async function () {
            const ergoText = Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'logic.ergo'), 'utf8');
            const ctoText = Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'model.cto'), 'utf8');
            const result = await Ergo.compile(ergoText, [ctoText], 'javascript');
            result.should.not.be.null;
            //result.output.should.equal('Hello Fred Blogs (Accord Project)');
        });
    });
    describe('#compileandlinkhellojs', function () {
        it('should compile and link a smart Ergo contract to JavaScript', async function () {
            const ergoText = Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'logic.ergo'), 'utf8');
            const ctoText = Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'model.cto'), 'utf8');
            const result = await Ergo.compileAndLink(ergoText, [ctoText], 'javascript');
            result.should.not.be.null;
            //result.output.should.equal('Hello Fred Blogs (Accord Project)');
        });
    });
    describe('#compilehellocicero', function () {
        it('should compile a smart Ergo contract to JavaScript for Cicero', async function () {
            const ergoText = Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'logic.ergo'), 'utf8');
            const ctoText = Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'model.cto'), 'utf8');
            const result = await Ergo.compile(ergoText, [ctoText], 'javascript_cicero');
            result.should.not.be.null;
            //result.output.should.equal('Hello Fred Blogs (Accord Project)');
        });
    });
    describe('#compilehellofail', function () {
        it('should fail when compiling a smart Ergo contract to JavaScript', async function () {
            const ergoText = Fs.readFileSync(Path.resolve(__dirname, 'data/latedeliveryandpenalty', 'logic.ergo'), 'utf8');
            const ctoText = Fs.readFileSync(Path.resolve(__dirname, 'data/latedeliveryandpenalty', 'model.cto'), 'utf8');
            const result = await Ergo.compile(ergoText, [ctoText], 'javascript');
            result.should.deep.equal({ 'error' : '[Compilation Error] Import not found: org.accordproject.base' });
            //result.output.should.equal('Hello Fred Blogs (Accord Project)');
        });
    });
    describe('#compilehelloandlinkfail', function () {
        it('should fail when compiling and linking a smart Ergo contract to JavaScript', async function () {
            const ergoText = Fs.readFileSync(Path.resolve(__dirname, 'data/latedeliveryandpenalty', 'logic.ergo'), 'utf8');
            const ctoText = Fs.readFileSync(Path.resolve(__dirname, 'data/latedeliveryandpenalty', 'model.cto'), 'utf8');
            const result = await Ergo.compileAndLink(ergoText, [ctoText], 'javascript');
            result.should.deep.equal({ 'error' : '[Compilation Error] Import not found: org.accordproject.base' });
            //result.output.should.equal('Hello Fred Blogs (Accord Project)');
        });
    });
    describe('#parsecto', function () {
        it('should parse CTO', async function () {
            const ctoText = Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'model.cto'), 'utf8');
            const result = await Ergo.parseCTO(ctoText);
            result.should.not.be.null;
            //result.output.should.equal('Hello Fred Blogs (Accord Project)');
        });
    });
});
