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

const Script = require('../lib/script');
const APModelManager = require('../lib/apmodelmanager');

const chai = require('chai');
const fs = require('fs');

chai.should();
chai.use(require('chai-things'));
chai.use(require('chai-as-promised'));

const jsSample = fs.readFileSync('./test/data/test.js','utf8');
const ctoSample = fs.readFileSync('./test/data/test.cto','utf8');
const ergoSample = fs.readFileSync('./test/data/test.ergo', 'utf8');

describe('Script', () => {
    let modelManager;

    beforeEach(async function () {
        modelManager = new APModelManager();
        modelManager.addModelFile(ctoSample,'test.cto',true);
    });

    describe('#constructor', () => {

        it('should instantiate a JavaScript script', async function() {
            const script = new Script(modelManager,'test.js','.js',jsSample);
            script.getLanguage().should.equal('.js');
            script.getIdentifier().should.equal('test.js');
            script.getContents().should.equal(jsSample);
            script.getTokens().length.should.equal(51);
        });

        it('should instantiate an Ergo script', async function() {
            const script = new Script(modelManager,'test.ergo','.ergo',ergoSample,'org.accordproject.helloemit.HelloWorld');
            script.getLanguage().should.equal('.ergo');
            script.getIdentifier().should.equal('test.ergo');
            script.getContractName().should.equal('org.accordproject.helloemit.HelloWorld');
            script.getContents().should.equal(ergoSample);
            script.getTokens().length.should.equal(0);
        });

        it('should fail to instantiate for empty script', async function() {
            (() => new Script(modelManager,'test.js','.js','')).should.throw('Empty script contents');
        });

        it('should fail to instantiate for buggy JavaScript', async function() {
            (() => new Script(modelManager,'test.js','.js','foo bar')).should.throw('Failed to parse test.js: Unexpected token');
        });

    });
    describe('#getFunctionDeclarations', () => {

        it('should instantiate a JavaScript script', async function() {
            const script = new Script(modelManager,'test.js','.js',jsSample);
            const decls = script.getFunctionDeclarations();
            decls.map(fd => fd.getName()).should.deep.equal(['paymentClause','__dispatch']);
            const decl = decls[0];
            decl.getThrows().should.equal('');
            decl.getLanguage().should.equal('.js');
            decl.getFunctionText().length.should.equal(169);
            decl.getVisibility().should.equal('+');
            decl.getDecorators().should.deep.equal(['param','param','param','param']);
            decl.getReturnType().should.equal('void');
            decl.getParameterNames().should.deep.equal(['context']);
            decl.getParameterTypes().should.deep.equal([
                'Context',
                'org.accordproject.copyrightlicense.PaymentRequest',
                'org.accordproject.copyrightlicense.PayOut',
                'Event'
            ]);
        });

        it('should fail to instantiate a JavaScript script', async function() {
            (() => new Script(null,'test.js','.js',jsSample)).should.throw('ModelManager is required.');
        });

    });

});
