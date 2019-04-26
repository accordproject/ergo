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

const ErgoError = require('../lib/ergoerror');
const ErgoCompiler = require('../lib/compiler');
const TemplateLogic = require('../lib/templatelogic');

const fs = require('fs');
const chai = require('chai');
const expect = chai.expect;

chai.should();
chai.use(require('chai-things'));
chai.use(require('chai-as-promised'));

const ctoSample = fs.readFileSync('./test/data/test.cto','utf8');
const ctoSample2 = fs.readFileSync('./test/data/test2.cto','utf8');
const ctoSample3 = fs.readFileSync('./test/data/test3.cto','utf8');
const ergoSample = fs.readFileSync('./test/data/test.ergo', 'utf8');
const ergoSample2 = fs.readFileSync('./test/data/test2.ergo', 'utf8');
const ergoSample3 = fs.readFileSync('./test/data/test3.ergo', 'utf8');
const jsSample = fs.readFileSync('./test/data/test.js', 'utf8');
const jsSample2 = fs.readFileSync('./test/data/test2.js', 'utf8');

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

        it('should load a logic file to the script manager', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addLogicFile(ergoSample,'test.ergo');
            templateLogic.compileLogicSync(false);
            templateLogic.getInvokeCall('helloworld').length.should.equal(233);
            templateLogic.getDispatchCall().length.should.equal(154);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(26120);
            templateLogic.compileLogicSync(false);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(26120);
        });

        it('should succeed creating a dispatch call for a JS logic file with a contract class (ES6)', () => {
            const templateLogic = new TemplateLogic('es6');
            templateLogic.addLogicFile(jsSample2,'test2.js');
            templateLogic.compileLogicSync(false);
            templateLogic.getDispatchCall().length.should.equal(188);
        });

        it('should succeed creating an invoke call for a JS logic file with a contract class (ES6)', () => {
            const templateLogic = new TemplateLogic('es6');
            templateLogic.addLogicFile(jsSample2,'test2.js');
            templateLogic.compileLogicSync(false);
            templateLogic.getInvokeCall().length.should.equal(204);
        });

        it('should succeed creating an invoke call for a JS logic file with a contract class (Cicero)', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addLogicFile(jsSample2,'test2.js');
            templateLogic.compileLogicSync(false);
            templateLogic.getInvokeCall().length.should.equal(204);
        });

        it('should fail creating a dispatch call for a JS logic file with no contract class (ES6)', () => {
            const templateLogic = new TemplateLogic('es6');
            templateLogic.addLogicFile(jsSample,'test.js');
            templateLogic.compileLogicSync(false);
            (() => templateLogic.getDispatchCall()).should.throw('Cannot create dispatch call for target: es6 without a contract name');
        });

        it('should fail creating an invoke call for a JS logic file with no contract class (ES6)', () => {
            const templateLogic = new TemplateLogic('es6');
            templateLogic.addLogicFile(jsSample,'test.js');
            templateLogic.compileLogicSync(false);
            (() => templateLogic.getInvokeCall()).should.throw('Cannot create invoke call for target: es6 without a contract name');
        });

        it('should fail creating an invoke call for a JS logic file with no contract class (Cicero)', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addLogicFile(jsSample,'test.js');
            templateLogic.compileLogicSync(false);
            (() => templateLogic.getInvokeCall()).should.throw('Cannot create invoke call for target: cicero without a contract name');
        });

        it('should fail to load a bogus logic file to the script manager', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addLogicFile(ergoSample2,'test2.ergo');
            try {
                templateLogic.compileLogicSync(false);
            } catch (error) {
                expect(error instanceof ErgoError).to.equal(true);
                expect(error.message).to.equal('Parse error (at file test2.ergo line 33 col 0). \n\n');
                expect(error.descriptor).to.deep.equal({
                    'kind': 'ParseError',
                    'locend': {
                        'character': 0,
                        'line': 33
                    },
                    'locstart': {
                        'character': 0,
                        'line': 33
                    },
                    'message': 'Parse error',
                    'verbose': 'Parse error (at file test2.ergo line 33 col 0). \n\n'
                });
            }
        });

        it('should load a logic file to the script manager (async)', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addLogicFile(ergoSample,'test.ergo');
            templateLogic.compileLogic(false).then((logicCode) => {
                templateLogic.getInvokeCall('helloworld').length.should.equal(233);
                templateLogic.getDispatchCall().length.should.equal(154);
                templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(26120);
                templateLogic.compileLogicSync(false);
                templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(26120);
            });
        });

        it('should fail to load a bogus logic file to the script manager (async)', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addLogicFile(ergoSample2,'test2.ergo');
            templateLogic.compileLogic(false).catch((error) => {
                expect(error instanceof ErgoError).to.equal(true);
                expect(error.message).to.equal('Parse error (at file test2.ergo line 33 col 0). \n\n');
                expect(error.descriptor).to.deep.equal({
                    'kind': 'ParseError',
                    'locend': {
                        'character': 0,
                        'line': 33
                    },
                    'locstart': {
                        'character': 0,
                        'line': 33
                    },
                    'message': 'Parse error',
                    'verbose': 'Parse error (at file test2.ergo line 33 col 0). \n\n'
                });
            });
        });

        it('should load a logic file to the script manager (with Ergo builtin)', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addErgoBuiltin();
            templateLogic.addLogicFile(ergoSample,'test3.ergo');
            templateLogic.compileLogicSync(false);
            templateLogic.getInvokeCall('helloworld').length.should.equal(233);
            templateLogic.getDispatchCall().length.should.equal(154);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(26120);
            templateLogic.compileLogicSync(false);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(26120);
        });

        it('should load a logic file (without extension) to the script manager', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addLogicFile(ergoSample,'test');
            templateLogic.compileLogicSync(false);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(26120);
        });

        it('should set the contract name', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addLogicFile(ergoSample,'test.ergo');
            const contractName = 'org.accordproject.helloemit.HelloWorld';
            templateLogic.setContractName(contractName);
            templateLogic.getContractName().should.equal(ErgoCompiler.contractCallName(contractName));
        });

        it('should set the compilation target to ES6 and recompile the logic', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addLogicFile(ergoSample,'test.ergo');
            templateLogic.getTarget().should.equal('cicero');
            templateLogic.compileLogicSync(false);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(26120);
            templateLogic.setTarget('es6', true);
            templateLogic.getTarget().should.equal('es6');
            const contractName = 'org.accordproject.helloemit.HelloWorld';
            templateLogic.setContractName(contractName);
            templateLogic.getContractName().should.equal(ErgoCompiler.contractCallName(contractName));
            templateLogic.getInvokeCall('helloworld').length.should.equal(233);
            templateLogic.getDispatchCall().length.should.equal(216);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(26961);
        });

        it('should fail to create init and dispatch for ES6 without a contract name', () => {
            const templateLogic = new TemplateLogic('es6');
            templateLogic.addLogicFile(ergoSample,'test.ergo');
            templateLogic.getTarget().should.equal('es6');
            templateLogic.compileLogicSync(false);
            templateLogic.getInvokeCall('helloworld').length.should.equal(233);
            templateLogic.getDispatchCall().length.should.equal(216);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(26961);
        });

        it('should set the compilation target to ES6 but not recompile the logic', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addLogicFile(ergoSample,'test.ergo');
            templateLogic.compileLogicSync(false);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(26120);
            templateLogic.setTarget('es6', false);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(26120);
        });

        it('should set the compilation target to ES5', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addLogicFile(ergoSample,'test.ergo');
            templateLogic.getTarget().should.equal('cicero');
            templateLogic.compileLogicSync(false);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(26120);
            templateLogic.setTarget('es5', true);
            templateLogic.getTarget().should.equal('es5');
            templateLogic.getInvokeCall('helloworld').length.should.equal(157);
            templateLogic.getDispatchCall().length.should.equal(140);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(26821);
        });

        it('should fail to create init code for Java', () => {
            const templateLogic = new TemplateLogic('java');
            templateLogic.addLogicFile(ergoSample,'test.ergo');
            templateLogic.getTarget().should.equal('java');
            templateLogic.compileLogicSync(false);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(10015);
            (() => templateLogic.getInvokeCall('helloworld')).should.throw('Unsupported target: java');
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

    describe('#updates', () => {
        let templateLogic;
        beforeEach(async function () {
            templateLogic = new TemplateLogic('cicero');
            templateLogic.addModelFile(ctoSample,'test.cto');
        });

        it('should update a model to the model manager', () => {
            const modelManager = templateLogic.getModelManager();
            templateLogic.updateModel(ctoSample,'test.cto');
            modelManager.getModels().map(x => x.name).should.deep.equal(['test.cto']);
            modelManager.getModels()[0].content.length.should.equal(175);
            templateLogic.updateModel(ctoSample3,'test.cto');
            modelManager.getModels().map(x => x.name).should.deep.equal(['test.cto']);
            modelManager.getModels()[0].content.length.should.equal(170);
            templateLogic.updateModel(ctoSample2,'test.cto');
            modelManager.getModels().map(x => x.name).should.deep.equal(['test.cto']);
            modelManager.getModels()[0].content.length.should.equal(173);
        });

        it('should add a model to the model manager', () => {
            const modelManager = templateLogic.getModelManager();
            templateLogic.updateModel(ctoSample2,'test2.cto');
            modelManager.getModels().map(x => x.name).should.deep.equal(['test.cto','test2.cto']);
            modelManager.getModels()[0].content.length.should.equal(175);
            modelManager.getModels()[1].content.length.should.equal(173);
        });

        it('should update a logic file in the script manager', () => {
            const templateLogic = new TemplateLogic('cicero');
            templateLogic.addLogicFile(ergoSample,'test.ergo');
            templateLogic.compileLogicSync(false);
            templateLogic.getInvokeCall('helloworld').length.should.equal(233);
            templateLogic.getDispatchCall().length.should.equal(154);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(26120);
            templateLogic.updateLogic(ergoSample,'test.ergo');
            templateLogic.compileLogicSync(false);
            templateLogic.updateLogic(ergoSample,'testNEW.ergo');
            templateLogic.compileLogicSync(false);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(26120);
            templateLogic.updateLogic(ergoSample3,'test.ergo');
            templateLogic.compileLogicSync(false);
            templateLogic.getScriptManager().getCompiledScript().getContents().length.should.equal(26120);
        });

    });

    describe('#validation', () => {
        let templateLogic;
        beforeEach(async function () {
            templateLogic = new TemplateLogic('cicero');
            templateLogic.addModelFile(ctoSample,'test.cto');
        });

        it('should succeed validating an input', () => {
            const input = {
                '$class': 'org.accordproject.copyrightlicense.PaymentRequest',
                'input': 'FOO'
            };
            const validInput = templateLogic.validateInput(input);
            validInput.should.not.be.null;
            validInput.should.have.property('timestamp');
            validInput.should.have.property('transactionId');
            validInput.should.deep.include(input);
        });
        it('should propagate null when validating an input', () => {
            expect(templateLogic.validateInput(null)).to.equal(null);
        });
        it('should fail validating an input with an unknown class', () => {
            const input = {
                '$class': 'org.accordproject.promissorynote.Payment',
                'amountPaid': { 'doubleValue' : 100.0, 'currencyCode' : 'USD' }
            };
            (() => templateLogic.validateInput(input)).should.throw('Namespace is not defined for type org.accordproject.promissorynote.Payment');
        });

        it('should succeed validating an output', () => {
            const output = {
                '$class': 'org.accordproject.copyrightlicense.PayOut',
                'amount': 200.00
            };
            const validOutput = templateLogic.validateOutput(output);
            validOutput.should.not.be.null;
            validOutput.should.have.property('timestamp');
            validOutput.should.have.property('transactionId');
            validOutput.should.deep.include(output);
        });
        it('should propagate null when validating an output', () => {
            expect(templateLogic.validateOutput(null)).to.equal(null);
        });
        it('should propagate strings or numbers when validating an output', () => {
            expect(templateLogic.validateOutput('test string')).to.equal('test string');
            expect(templateLogic.validateOutput(100.0)).to.equal(100.0);
        });
        it('should fail validating an output with an unknown class', () => {
            const output = {
                '$class': 'org.accordproject.promissorynote.Payment',
                'amountPaid': { 'doubleValue' : 100.0, 'currencyCode' : 'USD' }
            };
            (() => templateLogic.validateOutput(output)).should.throw('Namespace is not defined for type org.accordproject.promissorynote.Payment');
        });

        it('should succeed validating an input record', () => {
            const inputRecord = {
                'request': {
                    '$class': 'org.accordproject.copyrightlicense.PaymentRequest',
                    'input': 'FOO'
                },
                'x': 100.00,
                'y': 'foo'
            };
            const validInputRecord = templateLogic.validateInputRecord(inputRecord);
            validInputRecord.should.not.be.null;
            validInputRecord.should.have.property('request');
            validInputRecord.request.should.have.property('timestamp');
            validInputRecord.request.should.have.property('transactionId');
            validInputRecord.request.should.deep.include(inputRecord.request);
            validInputRecord.should.have.property('x');
            validInputRecord.x.should.equal(100.00);
            validInputRecord.should.have.property('y');
            validInputRecord.y.should.equal('foo');
        });
        it('should fail validating an input array', () => {
            const inputRecord = {
                'request': {
                    '$class': 'org.accordproject.promissorynote.Payment',
                    'amountPaid': { 'doubleValue' : 100.0, 'currencyCode' : 'USD' }
                },
                'x': 100.00,
                'y': 'foo'
            };
            (() => templateLogic.validateInputRecord(inputRecord)).should.throw('Namespace is not defined for type org.accordproject.promissorynote.Payment');
        });

        it('should succeed validating an output array', () => {
            const output = {
                '$class': 'org.accordproject.copyrightlicense.PayOut',
                'amount': 200.00
            };
            const validOutputArray = templateLogic.validateOutputArray([output]);
            validOutputArray.should.not.be.null;
            validOutputArray.length.should.equal(1);
            validOutputArray[0].should.have.property('timestamp');
            validOutputArray[0].should.have.property('transactionId');
            validOutputArray[0].should.deep.include(output);
            validOutputArray[0].should.deep.include(output);
        });
        it('should fail validating an output array', () => {
            const output = {
                '$class': 'org.accordproject.promissorynote.Payment',
                'amountPaid': { 'doubleValue' : 100.0, 'currencyCode' : 'USD' }
            };
            (() => templateLogic.validateOutputArray([output])).should.throw('Namespace is not defined for type org.accordproject.promissorynote.Payment');
        });
    });
});
