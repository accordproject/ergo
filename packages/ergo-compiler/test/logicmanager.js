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

const ErgoCompiler = require('../lib/compiler');
const LogicManager = require('../lib/logicmanager');

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
const ergoSample4 = fs.readFileSync('./test/data/test4.ergo', 'utf8');
const ergoSample5 = fs.readFileSync('./test/data/test5.ergo', 'utf8');
const jsSample = fs.readFileSync('./test/data/test.js', 'utf8');
const jsSample2 = fs.readFileSync('./test/data/test2.js', 'utf8');

describe('LogicManager', () => {
    describe('#constructors-accessors', () => {

        it('should create a template logic', () => {
            const logicManager = new LogicManager('cicero');
            logicManager.should.not.be.null;
            logicManager.getIntrospector().should.not.be.null;
            logicManager.getFactory().should.not.be.null;
            logicManager.getSerializer().should.not.be.null;
            logicManager.getScriptManager().should.not.be.null;
            logicManager.getModelManager().should.not.be.null;
        });

        it('should load a model to the model manager', () => {
            const logicManager = new LogicManager('cicero');
            logicManager.addModelFile(ctoSample,'test.cto');
            const modelManager = logicManager.getModelManager();
            modelManager.getModels().map(x => x.name).should.deep.equal(['test.cto']);
            modelManager.getModels()[0].content.length.should.equal(175);
        });

        it('should load a model to the model manager (bulk)', () => {
            const logicManager = new LogicManager('cicero');
            logicManager.addModelFiles([ctoSample],['test.cto']);
            const modelManager = logicManager.getModelManager();
            modelManager.getModels().map(x => x.name).should.deep.equal(['test.cto']);
            modelManager.getModels()[0].content.length.should.equal(175);
        });

        it('should load a logic file to the script manager', () => {
            const logicManager = new LogicManager('cicero');
            logicManager.addLogicFile(ergoSample,'test.ergo');
            logicManager.compileLogicSync(false);
            logicManager.getInvokeCall('helloworld').length.should.equal(250);
            logicManager.getDispatchCall().length.should.equal(172);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(31693);
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(31693);
        });

        it('should succeed creating a dispatch call for a JS logic file with a contract class (ES6)', () => {
            const logicManager = new LogicManager('es6');
            logicManager.addLogicFile(jsSample2,'test2.js');
            logicManager.compileLogicSync(false);
            logicManager.getDispatchCall().length.should.equal(206);
        });

        it('should succeed creating an invoke call for a JS logic file with a contract class (ES6)', () => {
            const logicManager = new LogicManager('es6');
            logicManager.addLogicFile(jsSample2,'test2.js');
            logicManager.compileLogicSync(false);
            logicManager.getInvokeCall().length.should.equal(221);
        });

        it('should succeed creating an invoke call for a JS logic file with a contract class (Cicero)', () => {
            const logicManager = new LogicManager('cicero');
            logicManager.addLogicFile(jsSample2,'test2.js');
            logicManager.compileLogicSync(false);
            logicManager.getInvokeCall().length.should.equal(221);
        });

        it('should fail creating a dispatch call for a JS logic file with no contract class (ES6)', () => {
            const logicManager = new LogicManager('es6');
            logicManager.addLogicFile(jsSample,'test.js');
            logicManager.compileLogicSync(false);
            (() => logicManager.getDispatchCall()).should.throw('Cannot create dispatch call for target: es6 without a contract name');
        });

        it('should fail creating an invoke call for a JS logic file with no contract class (ES6)', () => {
            const logicManager = new LogicManager('es6');
            logicManager.addLogicFile(jsSample,'test.js');
            logicManager.compileLogicSync(false);
            (() => logicManager.getInvokeCall()).should.throw('Cannot create invoke call for target: es6 without a contract name');
        });

        it('should fail creating an invoke call for a JS logic file with no contract class (Cicero)', () => {
            const logicManager = new LogicManager('cicero');
            logicManager.addLogicFile(jsSample,'test.js');
            logicManager.compileLogicSync(false);
            (() => logicManager.getInvokeCall()).should.throw('Cannot create invoke call for target: cicero without a contract name');
        });

        it('should fail to load a bogus logic file to the script manager', () => {
            const logicManager = new LogicManager('cicero');
            logicManager.addLogicFile(ergoSample2,'test2.ergo');
            try {
                logicManager.compileLogicSync(false);
            } catch (error) {
                expect(error.name).to.equal('ParseException');
                expect(error.message).to.equal('Parse error (at file test2.ergo line 33 col 0). \n\n');
                expect(error.fileName).to.equal('test2.ergo');
                expect(error.fileLocation).to.deep.equal({
                    'end': {
                        'column': 0,
                        'line': 33
                    },
                    'start': {
                        'column': 0,
                        'line': 33
                    }
                });
            }
        });

        it('should fail to load a logic file with a type error to the script manager', () => {
            const logicManager = new LogicManager('cicero');
            logicManager.addLogicFile(ergoSample4,'test4.ergo');
            try {
                logicManager.compileLogicSync(false);
            } catch (error) {
                expect(error.name).to.equal('TypeException');
                expect(error.message).to.equal('Type error (at file test4.ergo line 30 col 32). This operator received unexpected arguments of type `String\'  and `String\'.\n     return MyResponse{ output: "Hello " ++ contract.name ++ " (" ++ request.input + ")" }\n                                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ');
                expect(error.fileName).to.equal('test4.ergo');
                expect(error.fileLocation).to.deep.equal({
                    'end': {
                        'column': 88,
                        'line': 30
                    },
                    'start': {
                        'column': 32,
                        'line': 30
                    }
                });
            }
        });

        it('should fail to load a logic file with a compilation error to the script manager', () => {
            const logicManager = new LogicManager('cicero');
            logicManager.addLogicFile(ergoSample5,'test5.ergo');
            try {
                logicManager.compileLogicSync(false);
            } catch (error) {
                expect(error.name).to.equal('CompilerException');
                expect(error.message).to.equal('Compilation error (at file test5.ergo line 4 col 7). Import not found: NOTTHERE\nimport NOTTHERE.*\n       ^^^^^^^^^^');
                expect(error.fileLocation).to.deep.equal({
                    'end': {
                        'column': 17,
                        'line': 4
                    },
                    'start': {
                        'column': 7,
                        'line': 4
                    }
                });
            }
        });

        it('should load a logic file to the script manager (async)', () => {
            const logicManager = new LogicManager('cicero');
            logicManager.addLogicFile(ergoSample,'test.ergo');
            logicManager.compileLogic(false).then((logicCode) => {
                logicManager.getInvokeCall('helloworld').length.should.equal(250);
                logicManager.getDispatchCall().length.should.equal(172);
                logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(31693);
                logicManager.compileLogicSync(false);
                logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(31693);
            });
        });

        it('should fail to load a bogus logic file to the script manager (async)', () => {
            const logicManager = new LogicManager('cicero');
            logicManager.addLogicFile(ergoSample2,'test2.ergo');
            expect(logicManager.compileLogic(false)).to.be.eventually.rejectedWith(Error, 'Parse error (at file test2.ergo line 33 col 0). \n\n').and.have.property('name', 'ParseException');
        });

        it('should load a logic file to the script manager (with Ergo builtin)', () => {
            const logicManager = new LogicManager('cicero');
            logicManager.addErgoBuiltin();
            logicManager.addLogicFile(ergoSample,'test3.ergo');
            logicManager.compileLogicSync(false);
            logicManager.getInvokeCall('helloworld').length.should.equal(250);
            logicManager.getDispatchCall().length.should.equal(172);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(31693);
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(31693);
        });

        it('should load a logic file (without extension) to the script manager', () => {
            const logicManager = new LogicManager('cicero');
            logicManager.addLogicFile(ergoSample,'test');
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(31693);
        });

        it('should set the contract name', () => {
            const logicManager = new LogicManager('cicero');
            logicManager.addLogicFile(ergoSample,'test.ergo');
            const contractName = 'org.accordproject.helloemit.HelloWorld';
            logicManager.setContractName(contractName);
            logicManager.getContractName().should.equal(ErgoCompiler.contractCallName(contractName));
        });

        it('should set the compilation target to ES6 and recompile the logic', () => {
            const logicManager = new LogicManager('cicero');
            logicManager.addLogicFile(ergoSample,'test.ergo');
            logicManager.getTarget().should.equal('cicero');
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(31693);
            logicManager.setTarget('es6', true);
            logicManager.getTarget().should.equal('es6');
            const contractName = 'org.accordproject.helloemit.HelloWorld';
            logicManager.setContractName(contractName);
            logicManager.getContractName().should.equal(ErgoCompiler.contractCallName(contractName));
            logicManager.getInvokeCall('helloworld').length.should.equal(250);
            logicManager.getDispatchCall().length.should.equal(234);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(29998);
        });

        it('should fail to create init and dispatch for ES6 without a contract name', () => {
            const logicManager = new LogicManager('es6');
            logicManager.addLogicFile(ergoSample,'test.ergo');
            logicManager.getTarget().should.equal('es6');
            logicManager.compileLogicSync(false);
            logicManager.getInvokeCall('helloworld').length.should.equal(250);
            logicManager.getDispatchCall().length.should.equal(234);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(29998);
        });

        it('should set the compilation target to ES6 but not recompile the logic', () => {
            const logicManager = new LogicManager('cicero');
            logicManager.addLogicFile(ergoSample,'test.ergo');
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(31693);
            logicManager.setTarget('es6', false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(31693);
        });

        it('should set the compilation target to ES5', () => {
            const logicManager = new LogicManager('cicero');
            logicManager.addLogicFile(ergoSample,'test.ergo');
            logicManager.getTarget().should.equal('cicero');
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(31693);
            logicManager.setTarget('es5', true);
            logicManager.getTarget().should.equal('es5');
            logicManager.getInvokeCall('helloworld').length.should.equal(174);
            logicManager.getDispatchCall().length.should.equal(158);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(29852);
        });

        it('should fail to create init code for Java', () => {
            const logicManager = new LogicManager('java');
            logicManager.addLogicFile(ergoSample,'test.ergo');
            logicManager.getTarget().should.equal('java');
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(10717);
            (() => logicManager.getInvokeCall('helloworld')).should.throw('Unsupported target: java');
            (() => logicManager.getDispatchCall()).should.throw('Unsupported target: java');
        });

        it('should load a model without a name to the model manager', () => {
            const logicManager = new LogicManager('cicero');
            const modelManager = logicManager.getModelManager();
            modelManager.addModelFile(ctoSample,null,true);
            modelManager.getModels().map(x => x.name).should.deep.equal(['org.accordproject.copyrightlicense.cto']);
            modelManager.getModels()[0].content.length.should.equal(175);
        });
    });

    describe('#updates', () => {
        let logicManager;
        beforeEach(async function () {
            logicManager = new LogicManager('cicero');
            logicManager.addModelFile(ctoSample,'test.cto');
        });

        it('should update a model to the model manager', () => {
            const modelManager = logicManager.getModelManager();
            logicManager.updateModel(ctoSample,'test.cto');
            modelManager.getModels().map(x => x.name).should.deep.equal(['test.cto']);
            modelManager.getModels()[0].content.length.should.equal(175);
            logicManager.updateModel(ctoSample3,'test.cto');
            modelManager.getModels().map(x => x.name).should.deep.equal(['test.cto']);
            modelManager.getModels()[0].content.length.should.equal(369);
            logicManager.updateModel(ctoSample2,'test.cto');
            modelManager.getModels().map(x => x.name).should.deep.equal(['test.cto']);
            modelManager.getModels()[0].content.length.should.equal(173);
        });

        it('should add a model to the model manager', () => {
            const modelManager = logicManager.getModelManager();
            logicManager.updateModel(ctoSample2,'test2.cto');
            modelManager.getModels().map(x => x.name).should.deep.equal(['test.cto','test2.cto']);
            modelManager.getModels()[0].content.length.should.equal(175);
            modelManager.getModels()[1].content.length.should.equal(173);
        });

        it('should update a logic file in the script manager', () => {
            const logicManager = new LogicManager('cicero');
            logicManager.addLogicFile(ergoSample,'test.ergo');
            logicManager.compileLogicSync(false);
            logicManager.getInvokeCall('helloworld').length.should.equal(250);
            logicManager.getDispatchCall().length.should.equal(172);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(31693);
            logicManager.updateLogic(ergoSample,'test.ergo');
            logicManager.compileLogicSync(false);
            logicManager.updateLogic(ergoSample,'testNEW.ergo');
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(31693);
            logicManager.updateLogic(ergoSample3,'test.ergo');
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(31693);
        });

    });

    describe('#validation', () => {
        let logicManager;
        beforeEach(async function () {
            logicManager = new LogicManager('cicero');
            logicManager.addModelFile(ctoSample,'test.cto');
        });

        it('should succeed validating an input', () => {
            const input = {
                '$class': 'org.accordproject.copyrightlicense.PaymentRequest',
                'input': 'FOO'
            };
            const validInput = logicManager.validateInput(input);
            validInput.should.not.be.null;
            validInput.should.have.property('timestamp');
            validInput.should.have.property('transactionId');
            validInput.should.deep.include(input);
        });
        it('should propagate null when validating an input', () => {
            expect(logicManager.validateInput(null)).to.equal(null);
        });
        it('should fail validating an input with an unknown class', () => {
            const input = {
                '$class': 'org.accordproject.promissorynote.Payment',
                'amountPaid': { 'doubleValue' : 100.0, 'currencyCode' : 'USD' }
            };
            (() => logicManager.validateInput(input)).should.throw('Namespace is not defined for type org.accordproject.promissorynote.Payment');
        });

        it('should succeed validating an output', () => {
            const output = {
                '$class': 'org.accordproject.copyrightlicense.PayOut',
                'amount': 200.00
            };
            const validOutput = logicManager.validateOutput(output);
            validOutput.should.not.be.null;
            validOutput.should.have.property('timestamp');
            validOutput.should.have.property('transactionId');
            validOutput.should.deep.include(output);
        });
        it('should propagate null when validating an output', () => {
            expect(logicManager.validateOutput(null)).to.equal(null);
        });
        it('should propagate strings or numbers when validating an output', () => {
            expect(logicManager.validateOutput('test string')).to.equal('test string');
            expect(logicManager.validateOutput(100.0)).to.equal(100.0);
        });
        it('should fail validating an output with an unknown class', () => {
            const output = {
                '$class': 'org.accordproject.promissorynote.Payment',
                'amountPaid': { 'doubleValue' : 100.0, 'currencyCode' : 'USD' }
            };
            (() => logicManager.validateOutput(output)).should.throw('Namespace is not defined for type org.accordproject.promissorynote.Payment');
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
            const validInputRecord = logicManager.validateInputRecord(inputRecord);
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
            (() => logicManager.validateInputRecord(inputRecord)).should.throw('Namespace is not defined for type org.accordproject.promissorynote.Payment');
        });

        it('should succeed validating an output array', () => {
            const output = {
                '$class': 'org.accordproject.copyrightlicense.PayOut',
                'amount': 200.00
            };
            const validOutputArray = logicManager.validateOutputArray([output]);
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
            (() => logicManager.validateOutputArray([output])).should.throw('Namespace is not defined for type org.accordproject.promissorynote.Payment');
        });
    });
});
