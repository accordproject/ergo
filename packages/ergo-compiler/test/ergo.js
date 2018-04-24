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

    describe('#compilehello', function () {
        it('should compile a smart Ergo contract', async function () {
            const ergoText = Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'logic.ergo'), 'utf8');
            const ctoText = Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'model.cto'), 'utf8');
            const result = await Ergo.compile(ergoText, [ctoText], null, null, false);
            result.should.not.be.null;
            //result.output.should.equal('Hello Fred Blogs (Accord Project)');
        });
    });
    describe('#compilehello', function () {
        it('should compile a smart Ergo contract with contract/clause names', async function () {
            const ergoText = Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'logic.ergo'), 'utf8');
            const ctoText = Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'model.cto'), 'utf8');
            const result = await Ergo.compile(ergoText, [ctoText], 'HelloWorld', 'helloworld', false);
            result.should.not.be.null;
            //result.output.should.equal('Hello Fred Blogs (Accord Project)');
        });
    });
    describe('#compilehello', function () {
        it('should fail when compiling a smart Ergo contract', async function () {
            const ergoText = Fs.readFileSync(Path.resolve(__dirname, 'data/latedeliveryandpenalty', 'logic.ergo'), 'utf8');
            const ctoText = Fs.readFileSync(Path.resolve(__dirname, 'data/latedeliveryandpenalty', 'model.cto'), 'utf8');
            const result = await Ergo.compile(ergoText, [ctoText], 'LateDeliveryAndPenalty', 'latedeliveryandpenalty', false);
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
