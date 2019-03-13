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

const TemplateLogic = require('../lib/templatelogic');

const chai = require('chai');
const fs = require('fs');

chai.should();
chai.use(require('chai-things'));
chai.use(require('chai-as-promised'));

const ctoSample = fs.readFileSync('./test/data/test.cto','utf8');

describe('TemplateLogic', () => {

    describe('#constructors-accessors', () => {

        it('should create a template logic', () => {
            const templateLogic = new TemplateLogic();
            templateLogic.should.not.be.null;
            templateLogic.getIntrospector().should.not.be.null;
            templateLogic.getFactory().should.not.be.null;
            templateLogic.getSerializer().should.not.be.null;
            templateLogic.getScriptManager().should.not.be.null;
            templateLogic.getModelManager().should.not.be.null;
        });

        it('should load a model to the model manager', () => {
            const templateLogic = new TemplateLogic();
            const modelManager = templateLogic.getModelManager();
            modelManager.addModelFile(ctoSample,'test.cto',true);
            modelManager.getModels().map(x => x.name).should.deep.equal(['test.cto']);
            modelManager.getModels()[0].content.length.should.equal(175);
        });

        it('should load a model without a name to the model manager', () => {
            const templateLogic = new TemplateLogic();
            const modelManager = templateLogic.getModelManager();
            modelManager.addModelFile(ctoSample,null,true);
            modelManager.getModels().map(x => x.name).should.deep.equal(['org.accordproject.copyrightlicense.cto']);
            modelManager.getModels()[0].content.length.should.equal(175);
        });
    });
});