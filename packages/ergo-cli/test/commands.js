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

const Commands = require('../lib/commands');
const Chai = require('chai');

Chai.should();
Chai.use(require('chai-things'));
const Path = require('path');

describe('ergo', () => {

    afterEach(() => {});

    describe('#compilehello', function () {
        it('should compile a smart Ergo clause', async function () {
            const ergoPath = Path.resolve(__dirname, 'data/helloworld', 'logic.ergo');
            const ctoPath = Path.resolve(__dirname, 'data/helloworld', 'model.cto');
            const result = await Commands.compile(ergoPath, [ctoPath], 'HelloWorld', 'helloworld', false);
            result.should.not.be.null;
        });
        it('should compile a smart Ergo clause without cto', async function () {
            const ergoPath = Path.resolve(__dirname, 'data/helloworld', 'logic.ergo');
            const result = await Commands.compile(ergoPath, undefined, 'HelloWorld', 'helloworld', false);
            result.should.not.be.null;
        });
    });
    describe('#executehello', function () {
        it('should execute a smart Ergo clause', async function () {
            const ergoPath = Path.resolve(__dirname, 'data/helloworld', 'logic.ergo');
            const ctoPath = Path.resolve(__dirname, 'data/helloworld', 'model.cto');
            const clausePath = Path.resolve(__dirname, 'data/helloworld', 'contract.json');
            const requestPath = Path.resolve(__dirname, 'data/helloworld', 'request.json');
            const statePath = Path.resolve(__dirname, 'data/helloworld', 'state.json');
            const result = await Commands.execute(ergoPath, [ctoPath], clausePath, requestPath, statePath, 'HelloWorld', 'helloworld', false);
            result.response.output.should.equal('Hello Fred Blogs (Accord Project)');
        });
        it('should execute a smart Ergo clause without cto', async function () {
            const ergoPath = Path.resolve(__dirname, 'data/helloworld', 'logic.ergo');
            const clausePath = Path.resolve(__dirname, 'data/helloworld', 'contract.json');
            const requestPath = Path.resolve(__dirname, 'data/helloworld', 'request.json');
            const statePath = Path.resolve(__dirname, 'data/helloworld', 'state.json');
            const result = await Commands.execute(ergoPath, undefined, clausePath, requestPath, statePath, 'HelloWorld', 'helloworld', false);
            result.response.output.should.equal('Hello Fred Blogs (Accord Project)');
        });
    });
    describe('#parsecto', function () {
        it('should parse CTO', async function () {
            const ctoPath = Path.resolve(__dirname, 'data/helloworld', 'model.cto');
            const result = await Commands.parseCTO(ctoPath);
            result.should.not.be.null;
            //result.output.should.equal('Hello Fred Blogs (Accord Project)');
        });
    });
    describe('#parsectotofile', function () {
        it('should parse CTO to CTOJ', async function () {
            const ctoPath = Path.resolve(__dirname, 'data/helloworld', 'model.cto');
            const result = await Commands.parseCTOtoFile(ctoPath);
            result.should.not.be.null;
            //result.output.should.equal('Hello Fred Blogs (Accord Project)');
        });
    });
});
