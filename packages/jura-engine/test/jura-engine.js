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

const JuraEngine = require('../lib/jura-engine');
const Chai = require('chai');

Chai.should();
Chai.use(require('chai-things'));

const Fs = require('fs');
const Path = require('path');

describe('Execute', () => {

    afterEach(() => {});

    describe('#executehello', function () {
        it('should execute a smart Jura clause', async function () {
            const juraText = Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'logic.jura'), 'utf8');
            const jsonClause = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'clause.json'), 'utf8'));
            const jsonRequest = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, 'data/helloworld', 'request.json'), 'utf8'));
            const result = await JuraEngine.execute(juraText, jsonClause, jsonRequest, 'HelloWorld', 'helloworld', false);
            //result.should.not.be.null;
            result.output.should.equal('Hello Fred Blogs (Accord Project)');
        });
    });
});
