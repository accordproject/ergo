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
Chai.use(require('chai-as-promised'));

const Path = require('path');

const TESTS_DIR = '../../tests';

describe('#triggerhello', function () {
    it('should trigger a request to a smart Ergo contract', async function () {
        const ergoPath = Path.join(TESTS_DIR, 'helloworld', 'logic/logic.ergo');
        const ctoPath = Path.join(TESTS_DIR, 'helloworld', 'model/model.cto');
        const contractPath = { file: Path.join(TESTS_DIR, 'helloworld', 'data.json') };
        const requestPath = { file: Path.join(TESTS_DIR, 'helloworld', 'request.json') };
        const statePath = { file: Path.join(TESTS_DIR, 'helloworld', 'state.json') };
        const result = await Commands.trigger(null, [ergoPath, ctoPath], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]);
        result.response.output.should.equal('Hello Fred Blogs (Accord Project)');
    });
    it('should throw when executing a request to a smart Ergo contract with an illegal model', async function () {
        const ergoPath = Path.join(TESTS_DIR, 'helloworldErr', 'logic/logic.ergo');
        const ctoPath = Path.join(TESTS_DIR, 'helloworldErr', 'model/modelErr.cto');
        const contractPath = { file: Path.join(TESTS_DIR, 'helloworldErr', 'data.json') };
        const requestPath = { file: Path.join(TESTS_DIR, 'helloworldErr', 'request.json') };
        const statePath = { file: Path.join(TESTS_DIR, 'helloworldErr', 'state.json') };
        return Commands.trigger(null, [ergoPath, ctoPath], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]).should.be.rejectedWith('Expected "concerto", "namespace", comment, end of line, or whitespace but "E" found. File ../../tests/helloworldErr/model/modelErr.cto line 15 column 1');
    });
    it('should throw when executing a request to a smart Ergo contract without its cto', async function () {
        const ergoPath = Path.join(TESTS_DIR, 'helloworld', 'logic/logic.ergo');
        const contractPath = { file: Path.join(TESTS_DIR, 'helloworld', 'data.json') };
        const requestPath = { file: Path.join(TESTS_DIR, 'helloworld', 'request.json') };
        const statePath = { file: Path.join(TESTS_DIR, 'helloworld', 'state.json') };
        return Commands.trigger(null, [ergoPath], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]).should.be.rejectedWith('Compilation error (at file ../../tests/helloworld/logic/logic.ergo line 17 col 25). Cannot find type with name \'TemplateModel\'\ncontract HelloWorld over TemplateModel {\n                         ^^^^^^^^^^^^^  ');
    });
    it('should fail when Ergo logic is missing', async function () {
        const ctoPath = Path.join(TESTS_DIR, 'helloworld', 'model/model.cto');
        const contractPath = { file: Path.join(TESTS_DIR, 'helloworld', 'data.json') };
        const requestPath = { file: Path.join(TESTS_DIR, 'helloworld', 'request.json') };
        const statePath = { file: Path.join(TESTS_DIR, 'helloworld', 'state.json') };
        return Commands.trigger(null, [ctoPath], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]).should.be.rejectedWith('No input ergo found');
    });
});

describe('#triggerhellostate', function () {
    it('should trigger a smart Ergo contract with state once', async function () {
        const ergoPath = Path.join(TESTS_DIR, 'helloworldstate', 'logic/logic.ergo');
        const ctoPath = Path.join(TESTS_DIR, 'helloworldstate', 'model/model.cto');
        const contractPath = { file: Path.join(TESTS_DIR, 'helloworldstate', 'data.json') };
        const requestPath = { file: Path.join(TESTS_DIR, 'helloworldstate', 'request1.json') };
        const statePath = { file: Path.join(TESTS_DIR, 'helloworldstate', 'state1.json') };
        const result = await Commands.trigger(null, [ergoPath, ctoPath], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]);
        result.response.output.should.equal('Hello Fred Blogs (Accord Project) (1.0)');
    });
    it('should trigger a smart Ergo contract with state thrice', async function () {
        const ergoPath = Path.join(TESTS_DIR, 'helloworldstate', 'logic/logic.ergo');
        const ctoPath = Path.join(TESTS_DIR, 'helloworldstate', 'model/model.cto');
        const contractPath = { file: Path.join(TESTS_DIR, 'helloworldstate', 'data.json') };
        const requestPath = { file: Path.join(TESTS_DIR, 'helloworldstate', 'request1.json') };
        const requestPath2 = { file: Path.join(TESTS_DIR, 'helloworldstate', 'request2.json') };
        const statePath = { file: Path.join(TESTS_DIR, 'helloworldstate', 'state1.json') };
        const result = await Commands.trigger(null, [ergoPath, ctoPath], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath,requestPath2,requestPath2]);
        result.response.output.should.equal('Hello Fred Blogs (Linux Foundation) (3.0)');
    });
});

describe('#triggerinstallmentsale', function () {
    it('should initialize a smart Ergo contract state', async function () {
        const ergoPath = Path.join(TESTS_DIR, 'installment-sale', 'logic/logic.ergo');
        const ctoPath = Path.join(TESTS_DIR, 'installment-sale', 'model/model.cto');
        const contractPath = { file: Path.join(TESTS_DIR, 'installment-sale', 'data.json') };
        const result = await Commands.trigger(null, [ergoPath, ctoPath], contractPath, null, '1970-01-01T00:00:00Z', []);
        result.state.balance_remaining.should.equal(10000.00);
    });
    it('should initialize a smart Ergo contract and trigger one request', async function () {
        const ergoPath = Path.join(TESTS_DIR, 'installment-sale', 'logic/logic.ergo');
        const ctoPath = Path.join(TESTS_DIR, 'installment-sale', 'model/model.cto');
        const contractPath = { file: Path.join(TESTS_DIR, 'installment-sale', 'data.json') };
        const requestPath = { file: Path.join(TESTS_DIR, 'installment-sale', 'request.json') };
        const result = await Commands.trigger(null, [ergoPath, ctoPath], contractPath, null, '1970-01-01T00:00:00Z', [requestPath]);
        result.state.balance_remaining.should.equal(7612.499999999999);
    });
});

describe('#triggerpromissorynote', function () {
    it('should trigger a smart Ergo contract', async function () {
        const ergoPath = Path.join(TESTS_DIR, 'promissory-note', 'logic/logic.ergo');
        const ctoPath1 = Path.join(TESTS_DIR, 'promissory-note', 'model/business.cto');
        const ctoPath2 = Path.join(TESTS_DIR, 'promissory-note', 'model/model.cto');
        const contractPath = { file: Path.join(TESTS_DIR, 'promissory-note', 'data.json')};
        const requestPath = { file: Path.join(TESTS_DIR, 'promissory-note', 'request.json') };
        const statePath = { file: Path.join(TESTS_DIR, 'promissory-note', 'state.json') };
        const result = await Commands.trigger(null, [ergoPath, ctoPath1, ctoPath2], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]);
        result.response.outstandingBalance.should.equal(1425.4396822450633);
    });
});

describe('#triggerpromissorynotemodule', function () {
    it('should trigger a smart Ergo contract with two modules', async function () {
        const ergoPath1 = Path.join(TESTS_DIR, 'promissory-note', 'logic/money.ergo');
        const ergoPath2 = Path.join(TESTS_DIR, 'promissory-note', 'logic/logic3.ergo');
        const ctoPath1 = Path.join(TESTS_DIR, 'promissory-note', 'model/business.cto');
        const ctoPath2 = Path.join(TESTS_DIR, 'promissory-note', 'model/model.cto');
        const contractPath = { file: Path.join(TESTS_DIR, 'promissory-note', 'data.json')};
        const requestPath = { file: Path.join(TESTS_DIR, 'promissory-note', 'request.json') };
        const statePath = { file: Path.join(TESTS_DIR, 'promissory-note', 'state.json') };
        const result = await Commands.trigger(null, [ergoPath1, ergoPath2, ctoPath1, ctoPath2], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]);
        result.response.outstandingBalance.should.equal(1425.4396822450633);
    });
});

describe('#triggeracceptanceofdelivery', function () {
    it('should trigger a smart Ergo contract', async function () {
        const ergoPath = Path.join(TESTS_DIR, 'acceptance-of-delivery', 'logic/logic.ergo');
        const ctoPath = Path.join(TESTS_DIR, 'acceptance-of-delivery', 'model/model.cto');
        const contractPath = { file: Path.join(TESTS_DIR, 'acceptance-of-delivery', 'data.json') };
        const requestPath = { file: Path.join(TESTS_DIR, 'acceptance-of-delivery', 'request.json') };
        const statePath = { file: Path.join(TESTS_DIR, 'acceptance-of-delivery', 'state.json') };
        const result = await Commands.trigger(null, [ergoPath, ctoPath], contractPath, statePath, '2019-01-20T16:34:00-05:00', [requestPath]);
        result.response.status.should.equal('OUTSIDE_INSPECTION_PERIOD');
    });
    it('should trigger a smart Ergo contract', async function () {
        const ergoPath = Path.join(TESTS_DIR, 'acceptance-of-delivery', 'logic/logic.ergo');
        const ctoPath = Path.join(TESTS_DIR, 'acceptance-of-delivery', 'model/model.cto');
        const contractPath = { file: Path.join(TESTS_DIR, 'acceptance-of-delivery', 'data.json') };
        const requestPath = { file: Path.join(TESTS_DIR, 'acceptance-of-delivery', 'request.json') };
        const statePath = { file: Path.join(TESTS_DIR, 'acceptance-of-delivery', 'state.json') };
        const result = await Commands.trigger(null, [ergoPath, ctoPath], contractPath, statePath, '2019-01-11T16:34:00-05:00', [requestPath]);
        result.response.status.should.equal('PASSED_TESTING');
    });
});

describe('#invokehelloworld', function () {
    it('should invoke a clause in a smart Ergo contract (from directory)', async function () {
        const templatePath = Path.join(TESTS_DIR, 'helloworld3');
        const contractPath = { file: Path.join(TESTS_DIR, 'helloworld3', 'data.json') };
        const paramsPath = { file: Path.join(TESTS_DIR, 'helloworld3', 'params.json') };
        const statePath = { file: Path.join(TESTS_DIR, 'helloworld3', 'state.json') };
        const result = await Commands.invoke(templatePath, [], 'helloworld', contractPath, statePath, '1970-01-01T00:00:00Z', paramsPath, null);
        result.response.output.should.equal('Bonjour, Fred Blogs (Accord Project)');
    });
    it('should invoke a clause in a smart Ergo contract', async function () {
        const ergoPath = Path.join(TESTS_DIR, 'helloworld3', 'logic/logic3.ergo');
        const ctoPath = Path.join(TESTS_DIR, 'helloworld3', 'model/model.cto');
        const contractPath = { file: Path.join(TESTS_DIR, 'helloworld3', 'data.json') };
        const paramsPath = { file: Path.join(TESTS_DIR, 'helloworld3', 'params.json') };
        const statePath = { file: Path.join(TESTS_DIR, 'helloworld3', 'state.json') };
        const result = await Commands.invoke(null, [ergoPath, ctoPath], 'helloworld', contractPath, statePath, '1970-01-01T00:00:00Z', paramsPath, null);
        result.response.output.should.equal('Bonjour, Fred Blogs (Accord Project)');
    });
    it('should throw when invoking a clause in a smart Ergo contract with an illegal model', async function () {
        const ergoPath = Path.join(TESTS_DIR, 'helloworldErr', 'logic/logic.ergo');
        const ctoPath = Path.join(TESTS_DIR, 'helloworldErr', 'model/modelErr.cto');
        const contractPath = { file: Path.join(TESTS_DIR, 'helloworld', 'data.json') };
        const paramsPath = { file: Path.join(TESTS_DIR, 'helloworld', 'params.json') };
        const statePath = { file: Path.join(TESTS_DIR, 'helloworld', 'state.json') };
        return Commands.invoke(null, [ergoPath, ctoPath], 'helloworld', contractPath, statePath, '1970-01-01T00:00:00Z', paramsPath).should.be.rejectedWith('Expected "concerto", "namespace", comment, end of line, or whitespace but "E" found. File ../../tests/helloworldErr/model/modelErr.cto line 15 column 1');
    });
    it('should invoke a clause in a smart Ergo contract (JSON parameters)', async function () {
        const ergoPath = Path.join(TESTS_DIR, 'helloworld3', 'logic/logic3.ergo');
        const ctoPath = Path.join(TESTS_DIR, 'helloworld3', 'model/model.cto');
        const contractPath = { file: Path.join(TESTS_DIR, 'helloworld3', 'data.json') };
        const paramsJson = {
            content: `{
                    "request": {
                        "$class": "org.accordproject.helloworld.Request",
                        "input": "Accord Project"
                    },
                    "hello": "Bonjour,"
                }`
        };
        const statePath = { file: Path.join(TESTS_DIR, 'helloworld', 'state.json') };
        const result = await Commands.invoke(null, [ergoPath, ctoPath], 'helloworld', contractPath, statePath, '1970-01-01T00:00:00Z', paramsJson, null);
        result.response.output.should.equal('Bonjour, Fred Blogs (Accord Project)');
    });
    it('should throw when smart Ergo clause without a cto', async function () {
        const ergoPath = Path.join(TESTS_DIR, 'helloworld3', 'logic/logic3.ergo');
        const contractPath = { file: Path.join(TESTS_DIR, 'helloworld3', 'data.json') };
        const paramsPath = { file: Path.join(TESTS_DIR, 'helloworld3', 'params.json') };
        const statePath = { file: Path.join(TESTS_DIR, 'helloworld3', 'state.json') };
        return Commands.invoke(null, [ergoPath], 'helloworld', contractPath, statePath, '1970-01-01T00:00:00Z', paramsPath).should.be.rejectedWith('Compilation error (at file ../../tests/helloworld3/logic/logic3.ergo line 17 col 25). Cannot find type with name \'TemplateModel\'\ncontract HelloWorld over TemplateModel {\n                         ^^^^^^^^^^^^^  ');
    });
    it('should fail when Ergo logic is missing', async function () {
        const ctoPath = Path.join(TESTS_DIR, 'helloworld', 'model/model.cto');
        const contractPath = { file: Path.join(TESTS_DIR, 'helloworld', 'data.json') };
        const paramsPath = { file: Path.join(TESTS_DIR, 'helloworld', 'params.json') };
        const statePath = { file: Path.join(TESTS_DIR, 'helloworld', 'state.json') };
        return Commands.invoke(null, [ctoPath], 'helloworld', contractPath, statePath, '1970-01-01T00:00:00Z', paramsPath, null).should.be.rejectedWith('No input ergo found');
    });
});

describe('#initinstallmentsale', function () {
    it('should invoke init', async function () {
        const ergoPath = Path.join(TESTS_DIR, 'installment-sale', 'logic/logic.ergo');
        const ctoPath = Path.join(TESTS_DIR, 'installment-sale', 'model/model.cto');
        const contractPath = { file: Path.join(TESTS_DIR, 'installment-sale', 'data.json') };
        const paramsPath = { file: Path.join(TESTS_DIR, 'installment-sale', 'params.json') };
        const result = await Commands.initialize(null, [ergoPath, ctoPath], contractPath, '1970-01-01T00:00:00Z', paramsPath);
        result.state.balance_remaining.should.equal(10000.00);
    });
    it('should throw when initializing a smart Ergo contract with an illegal model', async function () {
        const ergoPath = Path.join(TESTS_DIR, 'installment-sale', 'logic/logic.ergo');
        const ctoPath = Path.join(TESTS_DIR, 'installment-sale', 'model/modelErr.cto');
        const contractPath = { file: Path.join(TESTS_DIR, 'installment-sale', 'data.json') };
        const paramsPath = { file: Path.join(TESTS_DIR, 'installment-sale', 'params.json') };
        return Commands.initialize(null, [ergoPath, ctoPath], contractPath, '1970-01-01T00:00:00Z', paramsPath).should.be.rejectedWith('Expected "concerto", "namespace", comment, end of line, or whitespace but "E" found. File ../../tests/installment-sale/model/modelErr.cto line 15 column 1');
    });
    it('should throw when initializing a smart Ergo clause without a cto', async function () {
        const ergoPath = Path.join(TESTS_DIR, 'installment-sale', 'logic/logic.ergo');
        const contractPath = { file: Path.join(TESTS_DIR, 'installment-sale', 'data.json') };
        const paramsPath = { file: Path.join(TESTS_DIR, 'installment-sale', 'params.json') };
        return Commands.initialize(null, [ergoPath], contractPath, '1970-01-01T00:00:00Z', paramsPath).should.be.rejectedWith('Compilation error (at file ../../tests/installment-sale/logic/logic.ergo line 19 col 30). Cannot find type with name \'TemplateModel\'\ncontract InstallmentSale over TemplateModel state InstallmentSaleState {\n                              ^^^^^^^^^^^^^                             ');
    });
    it('should fail when Ergo logic is missing', async function () {
        const ctoPath = Path.join(TESTS_DIR, 'installment-sale', 'model/model.cto');
        const contractPath = { file: Path.join(TESTS_DIR, 'installment-sale', 'data.json') };
        const paramsPath = { file: Path.join(TESTS_DIR, 'installment-sale', 'params.json') };
        return Commands.initialize(null, [ctoPath], contractPath, '1970-01-01T00:00:00Z', paramsPath).should.be.rejectedWith('No input ergo found');
    });
});

describe('#parsectotofile', function () {
    it('should parse CTO to CTOJ', async function () {
        const ctoPath = Path.join(TESTS_DIR, 'helloworld', 'model/model.cto');
        const result = await Commands.parseCTOtoFile(ctoPath);
        result.should.not.be.null;
    });
});
