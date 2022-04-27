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

const LogicManager = require('@accordproject/ergo-compiler').LogicManager;

const validateES6 = require('../lib/validateES6');

const fs = require('fs');
const chai = require('chai');
const expect = chai.expect;

chai.should();
chai.use(require('chai-things'));
chai.use(require('chai-as-promised'));

const ctoSample = fs.readFileSync('./test/data/test.cto','utf8');
const ctoSample3 = fs.readFileSync('./test/data/test3.cto','utf8');

describe('Validator', () => {
    describe('#baseValidation', () => {
        let modelManager;
        beforeEach(async function () {
            const logicManager = new LogicManager('es6');
            modelManager = logicManager.getModelManager();
            modelManager.addCTOModel(ctoSample,'test.cto');
        });

        it('should succeed validating an input', () => {
            const input = {
                '$class': 'org.accordproject.copyrightlicense.PaymentRequest',
                'input': 'FOO'
            };
            const validInput = validateES6.validateInput(modelManager, input);
            validInput.should.not.be.null;
            validInput.$data.should.have.property('$timestamp');
            validInput.$data.should.deep.include({ 'input': 'FOO' });
        });
        it('should propagate null when validating an input', () => {
            expect(validateES6.validateInput(modelManager, null)).to.equal(null);
        });
        it('should fail validating an input with an unknown class', () => {
            const input = {
                '$class': 'org.accordproject.promissorynote.Payment',
                'amountPaid': { 'doubleValue' : 100.0, 'currencyCode' : 'USD' }
            };
            (() => validateES6.validateInput(modelManager, input)).should.throw('Namespace is not defined for type "org.accordproject.promissorynote.Payment".');
        });

        it('should propagate null when validating a contract', () => {
            expect(validateES6.validateContract(modelManager, null)).to.equal(null);
        });

        it('should succeed validating an output', () => {
            const output = {
                '$class': { $coll: ['org.accordproject.copyrightlicense.PayOut'], $length: 1 },
                '$data' : { 'amount': 200.00 }
            };
            const validOutput = validateES6.validateOutput(modelManager, output);
            validOutput.should.not.be.null;
            validOutput.should.have.property('$timestamp');
            validOutput.should.deep.include({
                '$class': 'org.accordproject.copyrightlicense.PayOut',
                'amount': 200.00
            });
        });
        it('should propagate null when validating an output', () => {
            expect(validateES6.validateOutput(modelManager, null)).to.equal(null);
        });
        it('should propagate strings or numbers when validating an output', () => {
            expect(validateES6.validateOutput(modelManager, 'test string')).to.equal('test string');
            expect(validateES6.validateOutput(modelManager, 100.0)).to.equal(100.0);
        });
        it('should fail validating an output with an unknown class', () => {
            const output = {
                '$class': { $coll: ['org.accordproject.promissorynote.Payment'], $length: 1 },
                '$data': { 'amountPaid': { 'doubleValue' : 100.0, 'currencyCode' : 'USD' } }
            };
            (() => validateES6.validateOutput(modelManager, output)).should.throw('Namespace is not defined for type "org.accordproject.promissorynote.Payment".');
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
            const validInputRecord = validateES6.validateInputRecord(modelManager, inputRecord);
            validInputRecord.should.not.be.null;
            validInputRecord.should.have.property('request');
            validInputRecord.request.$data.should.have.property('$timestamp');
            validInputRecord.request.$data.should.deep.include({ 'input': 'FOO' });
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
            (() => validateES6.validateInputRecord(modelManager, inputRecord)).should.throw('Namespace is not defined for type "org.accordproject.promissorynote.Payment".');
        });

        it('should succeed validating an output array', () => {
            const output = {
                '$class': { $coll: ['org.accordproject.copyrightlicense.PayOut'], $length: 1 },
                '$data': { 'amount': 200.00 }
            };
            const expected = {
                '$class': 'org.accordproject.copyrightlicense.PayOut',
                'amount': 200.00
            };
            const validOutputArray = validateES6.validateOutputArray(modelManager, {$coll:[output],$length:1});
            validOutputArray.should.not.be.null;
            validOutputArray.length.should.equal(1);
            validOutputArray[0].should.have.property('$timestamp');
            validOutputArray[0].should.deep.include(expected);
        });
        it('should fail validating an output array', () => {
            const output = {
                '$class': { $coll: ['org.accordproject.promissorynote.Payment'], $length: 1 },
                '$data': { 'amountPaid': { 'doubleValue' : 100.0, 'currencyCode' : 'USD' } }
            };
            (() => validateES6.validateOutputArray(modelManager, {$coll:[output],$length:1})).should.throw('Namespace is not defined for type "org.accordproject.promissorynote.Payment".');
        });
    });

    describe('#ergoValidation', () => {
        let modelManager;
        beforeEach(async function () {
            const logicManager = new LogicManager('es6');
            modelManager = logicManager.getModelManager();
            modelManager.addCTOModel(ctoSample3,'test3.cto');
        });

        it('should succeed validating an input', () => {
            const input = {
                '$class': 'org.accordproject.copyrightlicense.FOO',
                'amount': 3.14,
                'someNumber': 3,
                'someArray': [0,1,2],
                'stuff': 'GRR',
                'relationship': { '$class' : 'org.accordproject.copyrightlicense.Baz', 'bazId': '1' }
            };
            const validInput = validateES6.validateInput(modelManager, input);
            validInput.should.not.be.null;
            validInput.$data.should.not.have.property('timestamp');
            validInput.$data.should.have.property('amount');
            validInput.$data.should.have.property('someNumber');
            validInput.$data.someNumber.should.have.property('$nat');
            validInput.$data.someNumber.$nat.should.equal(3);
            validInput.$data.someArray.should.deep.equal({$coll:[{'$nat':0},{'$nat':1},{'$nat':2}],$length:3});
            validInput.$data.relationship.should.deep.equal({'$class':{$coll:['org.accordproject.copyrightlicense.Baz'],$length:1}, '$data':{ 'bazId': '1', '$identifier': '1' } });
            const validOutput = validateES6.validateOutput(modelManager, validInput);
            validOutput.relationship.should.equal('resource:org.accordproject.copyrightlicense.Baz#1');
        });

        it('should succeed validating an contract', () => {
            const contract = {
                '$class': 'org.accordproject.copyrightlicense.FOO',
                'amount': 3.14,
                'someNumber': 3,
                'someArray': [0,1,2],
                'stuff': 'GRR',
                'relationship': { '$class' : 'org.accordproject.copyrightlicense.Baz', 'bazId': '1' }
            };
            const validContract = validateES6.validateContract(modelManager, contract);
            validContract.serialized.should.not.be.null;
            validContract.serialized.$data.should.not.have.property('timestamp');
            validContract.serialized.$data.should.have.property('amount');
            validContract.serialized.$data.should.have.property('someNumber');
            validContract.serialized.$data.someNumber.should.have.property('$nat');
            validContract.serialized.$data.someNumber.$nat.should.equal(3);
            validContract.serialized.$data.someArray.should.deep.equal({$coll:[{'$nat':0},{'$nat':1},{'$nat':2}],$length:3});
            validContract.serialized.$data.relationship.should.deep.equal({ '$class' : {$coll:['org.accordproject.copyrightlicense.Baz'],$length:1}, '$data' : { 'bazId': '1', '$identifier': '1' } });
        });
    });
});
