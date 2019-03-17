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
const ergoSample = fs.readFileSync('./test/data/test.ergo', 'utf8');

describe('TemplateLogic', () => {

    describe('#constructors-accessors', () => {

        it('should create a template logic', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.should.not.be.null;
            templateLogic.getIntrospector().should.not.be.null;
            templateLogic.getFactory().should.not.be.null;
            templateLogic.getSerializer().should.not.be.null;
            templateLogic.getScriptManager().should.not.be.null;
            templateLogic.getModelManager().should.not.be.null;
        });

        it('should load a model to the model manager', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addModelFile(ctoSample,'test.cto');
            const modelManager = templateLogic.getModelManager();
            modelManager.getModels().map(x => x.name).should.deep.equal(['test.cto']);
            modelManager.getModels()[0].content.length.should.equal(175);
        });

        it('should load a model to the model manager (bulk)', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addModelFiles([ctoSample],['test.cto']);
            const modelManager = templateLogic.getModelManager();
            modelManager.getModels().map(x => x.name).should.deep.equal(['test.cto']);
            modelManager.getModels()[0].content.length.should.equal(175);
        });

        it('should load a logic file to the model manager', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addLogicFile(ergoSample,'test.ergo');
            templateLogic.compileLogic(false);
            templateLogic.getInitCall().length.should.equal(63);
            templateLogic.getDispatchCall().length.should.equal(82);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(27672);
            templateLogic.compileLogic(false);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(27672);
        });

        it('should load a logic file to the model manager (with Ergo builtin)', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addErgoBuiltin();
            templateLogic.addLogicFile(ergoSample,'test3.ergo');
            templateLogic.compileLogic(false);
            templateLogic.getInitCall().length.should.equal(63);
            templateLogic.getDispatchCall().length.should.equal(82);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(27672);
            templateLogic.compileLogic(false);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(27672);
        });

        it('should load a logic file (without extension) to the model manager', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addLogicFile(ergoSample,'test');
            templateLogic.compileLogic(false);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(27672);
        });

        it('should set the contract name', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addLogicFile(ergoSample,'test.ergo');
            const contractName = 'org.accordproject.helloemit.HelloWorld';
            templateLogic.setContractName(contractName);
            templateLogic.getContractName().should.equal(contractName);
        });

        it('should set the compilation target to ES6 and recompile the logic', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addLogicFile(ergoSample,'test.ergo');
            templateLogic.getTarget().should.equal('cicero');
            templateLogic.compileLogic(false);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(27672);
            templateLogic.setTarget('es6', true);
            templateLogic.getTarget().should.equal('es6');
            const contractName = 'org.accordproject.helloemit.HelloWorld';
            templateLogic.setContractName(contractName);
            templateLogic.getInitCall().length.should.equal(123);
            templateLogic.getDispatchCall().length.should.equal(138);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(26797);
        });

        it('should fail to create init and dispatch for ES6 without a contract name', () => {
            const templateLogic = new TemplateLogic('es6');
            templateLogic.addLogicFile(ergoSample,'test.ergo');
            templateLogic.getTarget().should.equal('es6');
            templateLogic.compileLogic(false);
            (() => templateLogic.getInitCall()).should.throw('Cannot create init call for target: es6 without a contract name');
            (() => templateLogic.getDispatchCall()).should.throw('Cannot create dispatch call for target: es6 without a contract name');
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(26797);
        });

        it('should set the compilation target to ES6 but not recompile the logic', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addLogicFile(ergoSample,'test.ergo');
            templateLogic.compileLogic(false);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(27672);
            templateLogic.setTarget('es6', false);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(27672);
        });

        it('should set the compilation target to ES5', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addLogicFile(ergoSample,'test.ergo');
            templateLogic.getTarget().should.equal('cicero');
            templateLogic.compileLogic(false);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(27672);
            templateLogic.setTarget('es5', true);
            templateLogic.getTarget().should.equal('es5');
            templateLogic.getInitCall().length.should.equal(53);
            templateLogic.getDispatchCall().length.should.equal(68);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(26657);
        });

        it('should fail to create init code for Java', () => {
            const templateLogic = new TemplateLogic('java');
            templateLogic.addLogicFile(ergoSample,'test.ergo');
            templateLogic.getTarget().should.equal('java');
            templateLogic.compileLogic(false);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(10015);
            (() => templateLogic.getInitCall()).should.throw('Unsupported target: java');
            (() => templateLogic.getDispatchCall()).should.throw('Unsupported target: java');
        });

        it('should load a model without a name to the model manager', () => {
            const templateLogic = new TemplateLogic('cicero');
            const modelManager = templateLogic.getModelManager();
            modelManager.addModelFile(ctoSample,null,true);
            modelManager.getModels().map(x => x.name).should.deep.equal(['org.accordproject.copyrightlicense.cto']);
            modelManager.getModels()[0].content.length.should.equal(175);
        });
    });
});
