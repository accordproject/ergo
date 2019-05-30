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

const LogicManager = require('../lib/logicmanager');

const fs = require('fs');
const chai = require('chai');

chai.should();
chai.use(require('chai-things'));
chai.use(require('chai-as-promised'));

const ctoSample3 = fs.readFileSync('./test/data/test3.cto','utf8');

describe('Validator', () => {
    describe('#validationErgo', () => {
        it('should succeed validating an input', () => {
            const logicManager = new LogicManager('cicero');
            logicManager.addModelFile(ctoSample3,'test.cto');

            const input = {
                '$class': 'org.accordproject.copyrightlicense.FOO',
                'amount': 3.14,
                'someNumber': 3,
                'someArray': [0,1,2],
                'stuff': 'GRR',
                'relationship': { '$class' : 'org.accordproject.copyrightlicense.Baz', 'bazId': '1' }
            };
            const validInput = logicManager.validateInput(input);
            validInput.should.not.be.null;
            validInput.should.not.have.property('timestamp');
            validInput.should.have.property('amount');
            validInput.should.have.property('someNumber');
            validInput.someNumber.should.have.property('nat');
            validInput.someNumber.nat.should.equal(3);
            validInput.someArray.should.deep.equal([{'nat':0},{'nat':1},{'nat':2}]);
            validInput.relationship.should.deep.equal({ '$class' : 'org.accordproject.copyrightlicense.Baz', 'bazId': '1' });
            const validOutput = logicManager.validateOutput(validInput);
            validOutput.relationship.should.equal('resource:org.accordproject.copyrightlicense.Baz#1');
        });

        it('should succeed validating an contract', () => {
            const logicManager = new LogicManager('cicero');
            logicManager.addModelFile(ctoSample3,'test.cto');

            const contract = {
                '$class': 'org.accordproject.copyrightlicense.FOO',
                'amount': 3.14,
                'someNumber': 3,
                'someArray': [0,1,2],
                'stuff': 'GRR',
                'relationship': { '$class' : 'org.accordproject.copyrightlicense.Baz', 'bazId': '1' }
            };
            const validContract = logicManager.validateContract(contract);
            validContract.serialized.should.not.be.null;
            validContract.serialized.should.not.have.property('timestamp');
            validContract.serialized.should.have.property('amount');
            validContract.serialized.should.have.property('someNumber');
            validContract.serialized.someNumber.should.have.property('nat');
            validContract.serialized.someNumber.nat.should.equal(3);
            validContract.serialized.someArray.should.deep.equal([{'nat':0},{'nat':1},{'nat':2}]);
            validContract.serialized.relationship.should.deep.equal({ '$class' : 'org.accordproject.copyrightlicense.Baz', 'bazId': '1' });
        });
    });
});
