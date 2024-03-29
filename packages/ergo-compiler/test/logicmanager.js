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
const ErgoLoader = require('../lib/ergoloader');

const chai = require('chai');
const expect = chai.expect;

chai.should();
chai.use(require('chai-things'));
chai.use(require('chai-as-promised'));

const fs = require('fs');
const Path = require('path');

const TESTS_DIR = '../../tests';

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
            const logicManager = new LogicManager('es6');
            logicManager.should.not.be.null;
            logicManager.getIntrospector().should.not.be.null;
            logicManager.getScriptManager().should.not.be.null;
            logicManager.getModelManager().should.not.be.null;
        });

        it('should load a model to the model manager', () => {
            const logicManager = new LogicManager('es6');
            logicManager.getModelManager().addAPModelFile(ctoSample,'test.cto');
            const modelManager = logicManager.getModelManager();
            modelManager.getModels().map(x => x.name).should.deep.equal([
                '@models.accordproject.org.time@0.2.0.cto',
                '@models.accordproject.org.accordproject.money@0.2.0.cto',
                '@models.accordproject.org.accordproject.contract.cto',
                '@models.accordproject.org.accordproject.runtime.cto',
                '@org.accordproject.ergo.options.cto',
                'test.cto'
            ]);
            modelManager.getModels()[5].content.length.should.equal(175);
        });

        it('should load a model to the model manager (bulk)', () => {
            const logicManager = new LogicManager('es6');
            logicManager.getModelManager().addAPModelFiles([ctoSample],['test.cto']);
            const modelManager = logicManager.getModelManager();
            modelManager.getModels().map(x => x.name).should.deep.equal([
                '@models.accordproject.org.time@0.2.0.cto',
                '@models.accordproject.org.accordproject.money@0.2.0.cto',
                '@models.accordproject.org.accordproject.contract.cto',
                '@models.accordproject.org.accordproject.runtime.cto',
                '@org.accordproject.ergo.options.cto',
                'test.cto'
            ]);
            modelManager.getModels()[5].content.length.should.equal(175);
        });

        it('should load a logic file to the script manager', () => {
            const logicManager = new LogicManager('es6');
            logicManager.addLogicFile(ergoSample,'test.ergo');
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(47864);
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(47864);
            logicManager.registerCompiledLogicSync();
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(47864);
            logicManager.registerCompiledLogicSync();
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(47864);
        });

        it('should register a logic file to the script manager', () => {
            const logicManager = new LogicManager('es6');
            logicManager.addLogicFile(ergoSample,'test.ergo');
            logicManager.registerCompiledLogicSync();
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(47864);
        });

        it('should succeed creating a dispatch call for a JS logic file with a contract class (ES6)', () => {
            const logicManager = new LogicManager('es6');
            logicManager.addLogicFile(jsSample2,'test2.js');
            logicManager.compileLogicSync(false);
        });

        it('should succeed creating an invoke call for a JS logic file with a contract class (ES6)', () => {
            const logicManager = new LogicManager('es6');
            logicManager.addLogicFile(jsSample2,'test2.js');
            logicManager.compileLogicSync(false);
        });

        it('should succeed creating an invoke call for a JS logic file with a contract class (ES6)', () => {
            const logicManager = new LogicManager('es6');
            logicManager.addLogicFile(jsSample2,'test2.js');
            logicManager.compileLogicSync(false);
        });

        it('should fail creating an invoke call for a JS logic file with no contract class (ES6)', () => {
            const logicManager = new LogicManager('es6');
            logicManager.addLogicFile(jsSample,'test.js');
            logicManager.compileLogicSync(false);
        });

        it('should fail to load a bogus logic file to the script manager', () => {
            const logicManager = new LogicManager('es6');
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
            const logicManager = new LogicManager('es6');
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
            const logicManager = new LogicManager('es6');
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
            const logicManager = new LogicManager('es6');
            logicManager.addLogicFile(ergoSample,'test.ergo');
            logicManager.compileLogic(false).then((logicCode) => {
                logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(47864);
                logicManager.compileLogicSync(false);
                logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(47864);
            });
        });

        it('should fail to load a bogus logic file to the script manager (async)', () => {
            const logicManager = new LogicManager('es6');
            logicManager.addLogicFile(ergoSample2,'test2.ergo');
            expect(logicManager.compileLogic(false)).to.be.eventually.rejectedWith(Error, 'Parse error (at file test2.ergo line 33 col 0). \n\n').and.have.property('name', 'ParseException');
        });

        it('should load a logic file to the script manager (with Ergo builtin)', () => {
            const logicManager = new LogicManager('es6');
            logicManager.addLogicFile(ergoSample,'test3.ergo');
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(47864);
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(47864);
        });

        it('should load a logic file (without extension) to the script manager', () => {
            const logicManager = new LogicManager('es6');
            logicManager.addLogicFile(ergoSample,'test');
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(47864);
        });

        it('should set the contract name', () => {
            const logicManager = new LogicManager('es6');
            logicManager.addLogicFile(ergoSample,'test.ergo');
            const contractName = 'org.accordproject.helloemit.HelloWorld';
            logicManager.setContractName(contractName);
            logicManager.getContractName().should.equal(ErgoCompiler.contractCallName(contractName));
        });

        it('should set the compilation target to ES6 and recompile the logic', () => {
            const logicManager = new LogicManager('es6');
            logicManager.addLogicFile(ergoSample,'test.ergo');
            logicManager.getTarget().should.equal('es6');
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(47864);
            logicManager.setTarget('es6', true);
            logicManager.getTarget().should.equal('es6');
            const contractName = 'org.accordproject.helloemit.HelloWorld';
            logicManager.setContractName(contractName);
            logicManager.getContractName().should.equal(ErgoCompiler.contractCallName(contractName));
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(47864);
        });

        it('should fail to create init and dispatch for ES6 without a contract name', () => {
            const logicManager = new LogicManager('es6');
            logicManager.addLogicFile(ergoSample,'test.ergo');
            logicManager.getTarget().should.equal('es6');
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(47864);
        });

        it('should set the compilation target to ES6 but not recompile the logic', () => {
            const logicManager = new LogicManager('es6');
            logicManager.addLogicFile(ergoSample,'test.ergo');
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(47864);
            logicManager.setTarget('es6', false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(47864);
        });

        it('should fail to create init code for Java', () => {
            const logicManager = new LogicManager('java');
            logicManager.addLogicFile(ergoSample,'test.ergo');
            logicManager.getTarget().should.equal('java');
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(10596);
        });

        it('should load a model without a name to the model manager', () => {
            const logicManager = new LogicManager('es6');
            const modelManager = logicManager.getModelManager();
            modelManager.addCTOModel(ctoSample, null, true);
            modelManager.getModels().map(x => x.name).should.deep.equal([
                '@models.accordproject.org.time@0.2.0.cto',
                '@models.accordproject.org.accordproject.money@0.2.0.cto',
                '@models.accordproject.org.accordproject.contract.cto',
                '@models.accordproject.org.accordproject.runtime.cto',
                '@org.accordproject.ergo.options.cto',
                'org.accordproject.copyrightlicense.cto'
            ]);
            modelManager.getModels()[5].content.length.should.equal(175);
        });
    });

    describe('#loader-dir', () => {
        it('should load a directory with no formula', async function () {
            const logicManager = await ErgoLoader.fromDirectory(Path.join(TESTS_DIR,'acceptance-of-delivery'), {});
            const modelManager = logicManager.getModelManager();
            modelManager.getModels().map(x => x.name).should.deep.equal([
                '@models.accordproject.org.time@0.2.0.cto',
                '@models.accordproject.org.accordproject.money@0.2.0.cto',
                '@models.accordproject.org.accordproject.contract.cto',
                '@models.accordproject.org.accordproject.runtime.cto',
                '@org.accordproject.ergo.options.cto',
                'model.cto'
            ]);
            modelManager.getModels()[0].content.length.should.equal(1328);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(135676);
        });

        it('should load a directory with formula', async function () {
            const logicManager = await ErgoLoader.fromDirectory(Path.join(TESTS_DIR,'helloworldcontract'));
            const modelManager = logicManager.getModelManager();
            modelManager.getModels().map(x => x.name).should.deep.equal([
                '@models.accordproject.org.time@0.2.0.cto',
                '@models.accordproject.org.accordproject.money@0.2.0.cto',
                '@models.accordproject.org.accordproject.contract.cto',
                '@models.accordproject.org.accordproject.runtime.cto',
                '@org.accordproject.ergo.options.cto',
                'model.cto'
            ]);
            modelManager.getModels()[0].content.length.should.equal(1328);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(66768);
        });
    });

    describe('#loader-zip', () => {
        it('should load a Zip with no formula', async function () {
            const buffer = fs.readFileSync(Path.join(TESTS_DIR,'acceptance-of-delivery.zip'));
            const logicManager = await ErgoLoader.fromZip(buffer, {});
            const modelManager = logicManager.getModelManager();
            modelManager.getModels().map(x => x.name).should.deep.equal([
                '@models.accordproject.org.time@0.2.0.cto',
                '@models.accordproject.org.accordproject.money@0.2.0.cto',
                '@models.accordproject.org.accordproject.contract.cto',
                '@models.accordproject.org.accordproject.runtime.cto',
                '@org.accordproject.ergo.options.cto',
                'model.cto'
            ]);
            modelManager.getModels()[0].content.length.should.equal(1328);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(135676);
        });

        it('should load a Zip with formula', async function () {
            const buffer = fs.readFileSync(Path.join(TESTS_DIR,'helloworldcontract.zip'));
            const logicManager = await ErgoLoader.fromZip(buffer);
            const modelManager = logicManager.getModelManager();
            modelManager.getModels().map(x => x.name).should.deep.equal([
                '@models.accordproject.org.time@0.2.0.cto',
                '@models.accordproject.org.accordproject.money@0.2.0.cto',
                '@models.accordproject.org.accordproject.contract.cto',
                '@models.accordproject.org.accordproject.runtime.cto',
                '@org.accordproject.ergo.options.cto',
                'model.cto'
            ]);
            modelManager.getModels()[0].content.length.should.equal(1328);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(66768);
        });
    });


    describe('#loader-files', () => {
        it('should load files with no formula', async function () {
            const files = [
                Path.join(TESTS_DIR,'acceptance-of-delivery/model/model.cto'),
                Path.join(TESTS_DIR,'acceptance-of-delivery/logic/logic.ergo'),
            ];
            const logicManager = await ErgoLoader.fromFiles(files, {});
            const modelManager = logicManager.getModelManager();
            modelManager.getModels().map(x => x.name).should.deep.equal([
                '@models.accordproject.org.time@0.2.0.cto',
                '@models.accordproject.org.accordproject.money@0.2.0.cto',
                '@models.accordproject.org.accordproject.contract.cto',
                '@models.accordproject.org.accordproject.runtime.cto',
                '@org.accordproject.ergo.options.cto',
                'model.cto'
            ]);
            modelManager.getModels()[0].content.length.should.equal(1328);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(135676);
        });

        it('should load a Zip with formula', async function () {
            const files = [
                Path.join(TESTS_DIR,'helloworldcontract/model/model.cto'),
                Path.join(TESTS_DIR,'helloworldcontract/logic/logic.ergo'),
                Path.join(TESTS_DIR,'helloworldcontract/text/formula.tem'),
            ];
            const logicManager = await ErgoLoader.fromFiles(files);
            const modelManager = logicManager.getModelManager();
            modelManager.getModels().map(x => x.name).should.deep.equal([
                '@models.accordproject.org.time@0.2.0.cto',
                '@models.accordproject.org.accordproject.money@0.2.0.cto',
                '@models.accordproject.org.accordproject.contract.cto',
                '@models.accordproject.org.accordproject.runtime.cto',
                '@org.accordproject.ergo.options.cto',
                'model.cto'
            ]);
            modelManager.getModels()[0].content.length.should.equal(1328);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(66768);
        });
    });

    describe('#updates', () => {
        let logicManager;
        beforeEach(async function () {
            logicManager = new LogicManager('es6');
            logicManager.getModelManager().addAPModelFile(ctoSample,'test.cto');
        });

        it('should update a model to the model manager', () => {
            const modelManager = logicManager.getModelManager();
            logicManager.getModelManager().updateModel(ctoSample,'test.cto');
            modelManager.getModels().map(x => x.name).should.deep.equal([
                '@models.accordproject.org.time@0.2.0.cto',
                '@models.accordproject.org.accordproject.money@0.2.0.cto',
                '@models.accordproject.org.accordproject.contract.cto',
                '@models.accordproject.org.accordproject.runtime.cto',
                '@org.accordproject.ergo.options.cto',
                'test.cto'
            ]);
            modelManager.getModels()[5].content.length.should.equal(175);
            logicManager.getModelManager().updateModel(ctoSample3,'test.cto');
            modelManager.getModels().map(x => x.name).should.deep.equal([
                '@models.accordproject.org.time@0.2.0.cto',
                '@models.accordproject.org.accordproject.money@0.2.0.cto',
                '@models.accordproject.org.accordproject.contract.cto',
                '@models.accordproject.org.accordproject.runtime.cto',
                '@org.accordproject.ergo.options.cto',
                'test.cto'
            ]);
            modelManager.getModels()[5].content.length.should.equal(369);
            logicManager.getModelManager().updateModel(ctoSample2,'test.cto');
            modelManager.getModels().map(x => x.name).should.deep.equal([
                '@models.accordproject.org.time@0.2.0.cto',
                '@models.accordproject.org.accordproject.money@0.2.0.cto',
                '@models.accordproject.org.accordproject.contract.cto',
                '@models.accordproject.org.accordproject.runtime.cto',
                '@org.accordproject.ergo.options.cto',
                'test.cto'
            ]);
            modelManager.getModels()[5].content.length.should.equal(173);
        });

        it('should add a model to the model manager', () => {
            const modelManager = logicManager.getModelManager();
            logicManager.getModelManager().updateModel(ctoSample2,'test2.cto');
            modelManager.getModels().map(x => x.name).should.deep.equal([
                '@models.accordproject.org.time@0.2.0.cto',
                '@models.accordproject.org.accordproject.money@0.2.0.cto',
                '@models.accordproject.org.accordproject.contract.cto',
                '@models.accordproject.org.accordproject.runtime.cto',
                '@org.accordproject.ergo.options.cto',
                'test.cto',
                'test2.cto'
            ]);
            modelManager.getModels()[5].content.length.should.equal(175);
            modelManager.getModels()[6].content.length.should.equal(173);
        });

        it('should update a logic file in the script manager', () => {
            const logicManager = new LogicManager('es6');
            logicManager.addLogicFile(ergoSample,'test.ergo');
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(47864);
            logicManager.updateLogic(ergoSample,'test.ergo');
            logicManager.compileLogicSync(false);
            logicManager.updateLogic(ergoSample,'testNEW.ergo');
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(47864);
            logicManager.updateLogic(ergoSample3,'test.ergo');
            logicManager.compileLogicSync(false);
            logicManager.getScriptManager().getCompiledScript().getContents().length.should.equal(47864);
        });

    });

});
