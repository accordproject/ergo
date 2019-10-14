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

describe('ergo', () => {

    afterEach(() => {});

    describe('#executehello', function () {
        it('should execute a request to a smart Ergo contract', async function () {
            const ergoPath = Path.join('test/examples/helloworld', 'logic/logic.ergo');
            const ctoPath = Path.join('test/examples/helloworld', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/helloworld', 'data.json') };
            const requestPath = { file: Path.join('test/examples/helloworld', 'request.json') };
            const statePath = { file: Path.join('test/examples/helloworld', 'state.json') };
            const result = await Commands.request(null, [ergoPath, ctoPath], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]);
            result.response.output.should.equal('Hello Fred Blogs (Accord Project)');
        });
        it('should throw when executing a request to a smart Ergo contract with an illegal model', async function () {
            const ergoPath = Path.join('test/examples/helloworld', 'logic/logic.ergo');
            const ctoPath = Path.join('test/examples/helloworld', 'model/modelErr.cto');
            const contractPath = { file: Path.join('test/examples/helloworld', 'data.json') };
            const requestPath = { file: Path.join('test/examples/helloworld', 'request.json') };
            const statePath = { file: Path.join('test/examples/helloworld', 'state.json') };
            return Commands.request(null, [ergoPath, ctoPath], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]).should.be.rejectedWith('Expected "namespace", comment, end of line, or whitespace but "E" found. File test/examples/helloworld/model/modelErr.cto line 15 column 1');
        });
        it('should throw when executing a request to a smart Ergo contract without its cto', async function () {
            const ergoPath = Path.join('test/examples/helloworld', 'logic/logic.ergo');
            const contractPath = { file: Path.join('test/examples/helloworld', 'data.json') };
            const requestPath = { file: Path.join('test/examples/helloworld', 'request.json') };
            const statePath = { file: Path.join('test/examples/helloworld', 'state.json') };
            return Commands.request(null, [ergoPath], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]).should.be.rejectedWith('Compilation error (at file test/examples/helloworld/logic/logic.ergo line 17 col 25). Cannot find type with name \'TemplateModel\'\ncontract HelloWorld over TemplateModel {\n                         ^^^^^^^^^^^^^  ');
        });
        it('should fail when Ergo logic is missing', async function () {
            const ctoPath = Path.join('test/examples/helloworld', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/helloworld', 'data.json') };
            const requestPath = { file: Path.join('test/examples/helloworld', 'request.json') };
            const statePath = { file: Path.join('test/examples/helloworld', 'state.json') };
            return Commands.request(null, [ctoPath], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]).should.be.rejectedWith('No input ergo found');
        });
    });
    describe('#executehellostate', function () {
        it('should execute a smart Ergo contract with state once', async function () {
            const ergoPath = Path.join('test/examples/helloworldstate', 'logic/logic.ergo');
            const ctoPath = Path.join('test/examples/helloworldstate', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/helloworldstate', 'data.json') };
            const requestPath = { file: Path.join('test/examples/helloworldstate', 'request1.json') };
            const statePath = { file: Path.join('test/examples/helloworldstate', 'state1.json') };
            const result = await Commands.request(null, [ergoPath, ctoPath], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]);
            result.response.output.should.equal('Hello Fred Blogs (Accord Project) (1.0)');
        });
        it('should execute a smart Ergo contract with state thrice', async function () {
            const ergoPath = Path.join('test/examples/helloworldstate', 'logic/logic.ergo');
            const ctoPath = Path.join('test/examples/helloworldstate', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/helloworldstate', 'data.json') };
            const requestPath = { file: Path.join('test/examples/helloworldstate', 'request1.json') };
            const requestPath2 = { file: Path.join('test/examples/helloworldstate', 'request2.json') };
            const statePath = { file: Path.join('test/examples/helloworldstate', 'state1.json') };
            const result = await Commands.request(null, [ergoPath, ctoPath], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath,requestPath2,requestPath2]);
            result.response.output.should.equal('Hello Fred Blogs (Linux Foundation) (3.0)');
        });
    });
    describe('#executeinstallmentsale', function () {
        it('should initialize a smart Ergo contract state', async function () {
            const ergoPath = Path.join('test/examples/installment-sale', 'logic/logic.ergo');
            const ctoPath = Path.join('test/examples/installment-sale', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/installment-sale', 'data.json') };
            const result = await Commands.request(null, [ergoPath, ctoPath], contractPath, null, '1970-01-01T00:00:00Z', []);
            result.state.balance_remaining.should.equal(10000.00);
        });
        it('should initialize a smart Ergo contract and execute one request', async function () {
            const ergoPath = Path.join('test/examples/installment-sale', 'logic/logic.ergo');
            const ctoPath = Path.join('test/examples/installment-sale', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/installment-sale', 'data.json') };
            const requestPath = { file: Path.join('test/examples/installment-sale', 'request.json') };
            const result = await Commands.request(null, [ergoPath, ctoPath], contractPath, null, '1970-01-01T00:00:00Z', [requestPath]);
            result.state.balance_remaining.should.equal(7612.499999999999);
        });
    });
    describe('#executepromissorynote', function () {
        it('should execute a smart Ergo contract', async function () {
            const ergoPath = Path.join('test/examples/promissory-note', 'logic/logic.ergo');
            const ctoPath1 = Path.join('test/examples/promissory-note', 'model/business.cto');
            const ctoPath2 = Path.join('test/examples/promissory-note', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/promissory-note', 'data.json')};
            const requestPath = { file: Path.join('test/examples/promissory-note', 'request.json') };
            const statePath = { file: Path.join('test/examples/promissory-note', 'state.json') };
            const result = await Commands.request(null, [ergoPath, ctoPath1, ctoPath2], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]);
            result.response.outstandingBalance.should.equal(1425.4396822450633);
        });
    });
    describe('#executepromissorynotemodule', function () {
        it('should execute a smart Ergo contract with two modules', async function () {
            const ergoPath1 = Path.join('test/examples/promissory-note', 'logic/money.ergo');
            const ergoPath2 = Path.join('test/examples/promissory-note', 'logic/logic3.ergo');
            const ctoPath1 = Path.join('test/examples/promissory-note', 'model/business.cto');
            const ctoPath2 = Path.join('test/examples/promissory-note', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/promissory-note', 'data.json')};
            const requestPath = { file: Path.join('test/examples/promissory-note', 'request.json') };
            const statePath = { file: Path.join('test/examples/promissory-note', 'state.json') };
            const result = await Commands.request(null, [ergoPath1, ergoPath2, ctoPath1, ctoPath2], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]);
            result.response.outstandingBalance.should.equal(1425.4396822450633);
        });
    });
    describe('#executeacceptanceofdelivery', function () {
        it('should execute a smart Ergo contract', async function () {
            const ergoPath = Path.join('test/examples/acceptance-of-delivery', 'logic/logic.ergo');
            const ctoPath = Path.join('test/examples/acceptance-of-delivery', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/acceptance-of-delivery', 'data.json') };
            const requestPath = { file: Path.join('test/examples/acceptance-of-delivery', 'request.json') };
            const statePath = { file: Path.join('test/examples/acceptance-of-delivery', 'state.json') };
            const result = await Commands.request(null, [ergoPath, ctoPath], contractPath, statePath, '2019-01-20T16:34:00-05:00', [requestPath]);
            result.response.status.should.equal('OUTSIDE_INSPECTION_PERIOD');
        });
        it('should execute a smart Ergo contract', async function () {
            const ergoPath = Path.join('test/examples/acceptance-of-delivery', 'logic/logic.ergo');
            const ctoPath = Path.join('test/examples/acceptance-of-delivery', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/acceptance-of-delivery', 'data.json') };
            const requestPath = { file: Path.join('test/examples/acceptance-of-delivery', 'request.json') };
            const statePath = { file: Path.join('test/examples/acceptance-of-delivery', 'state.json') };
            const result = await Commands.request(null, [ergoPath, ctoPath], contractPath, statePath, '2019-01-11T16:34:00-05:00', [requestPath]);
            result.response.status.should.equal('PASSED_TESTING');
        });
    });
    describe('#invokehelloworld', function () {
        it('should invoke a clause in a smart Ergo contract', async function () {
            const ergoPath = Path.join('test/examples/helloworld', 'logic/logic4.ergo');
            const ctoPath = Path.join('test/examples/helloworld', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/helloworld', 'data.json') };
            const paramsPath = { file: Path.join('test/examples/helloworld', 'params.json') };
            const statePath = { file: Path.join('test/examples/helloworld', 'state.json') };
            const result = await Commands.invoke(null, [ergoPath, ctoPath], 'helloworld', contractPath, statePath, '1970-01-01T00:00:00Z', paramsPath, null);
            result.response.output.should.equal('Bonjour, Fred Blogs (Accord Project)');
        });
        it('should throw when invoking a clause in a smart Ergo contract with an illegal model', async function () {
            const ergoPath = Path.join('test/examples/helloworld', 'logic/logic.ergo');
            const ctoPath = Path.join('test/examples/helloworld', 'model/modelErr.cto');
            const contractPath = { file: Path.join('test/examples/helloworld', 'data.json') };
            const paramsPath = { file: Path.join('test/examples/helloworld', 'params.json') };
            const statePath = { file: Path.join('test/examples/helloworld', 'state.json') };
            return Commands.invoke(null, [ergoPath, ctoPath], 'helloworld', contractPath, statePath, '1970-01-01T00:00:00Z', paramsPath).should.be.rejectedWith('Expected "namespace", comment, end of line, or whitespace but "E" found. File test/examples/helloworld/model/modelErr.cto line 15 column 1');
        });
        it('should invoke a clause in a smart Ergo contract (JSON parameters)', async function () {
            const ergoPath = Path.join('test/examples/helloworld', 'logic/logic4.ergo');
            const ctoPath = Path.join('test/examples/helloworld', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/helloworld', 'data.json') };
            const paramsJson = {
                content: `{
                    "request": {
                        "$class": "org.accordproject.helloworld.Request",
                        "input": "Accord Project"
                    },
                    "hello": "Bonjour,"
                }`
            };
            const statePath = { file: Path.join('test/examples/helloworld', 'state.json') };
            const result = await Commands.invoke(null, [ergoPath, ctoPath], 'helloworld', contractPath, statePath, '1970-01-01T00:00:00Z', paramsJson, null);
            result.response.output.should.equal('Bonjour, Fred Blogs (Accord Project)');
        });
        it('should throw when smart Ergo clause without a cto', async function () {
            const ergoPath = Path.join('test/examples/helloworld', 'logic/logic4.ergo');
            const contractPath = { file: Path.join('test/examples/helloworld', 'data.json') };
            const paramsPath = { file: Path.join('test/examples/helloworld', 'params.json') };
            const statePath = { file: Path.join('test/examples/helloworld', 'state.json') };
            return Commands.invoke(null, [ergoPath], 'helloworld', contractPath, statePath, '1970-01-01T00:00:00Z', paramsPath).should.be.rejectedWith('Compilation error (at file test/examples/helloworld/logic/logic4.ergo line 17 col 25). Cannot find type with name \'TemplateModel\'\ncontract HelloWorld over TemplateModel {\n                         ^^^^^^^^^^^^^  ');
        });
        it('should fail when Ergo logic is missing', async function () {
            const ctoPath = Path.join('test/examples/helloworld', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/helloworld', 'data.json') };
            const paramsPath = { file: Path.join('test/examples/helloworld', 'params.json') };
            const statePath = { file: Path.join('test/examples/helloworld', 'state.json') };
            return Commands.invoke(null, [ctoPath], 'helloworld', contractPath, statePath, '1970-01-01T00:00:00Z', paramsPath, null).should.be.rejectedWith('No input ergo found');
        });
    });
    describe('#generatetext', function () {
        it('should generate text for a smart Ergo contract', async function () {
            const ergoPath = Path.join('test/examples/interests', 'logic/logic.ergo');
            const ergoPath2 = Path.join('test/examples/interests', 'logic/interests.ergo');
            const ctoPath = Path.join('test/examples/interests', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/interests', 'data.json') };
            const result = await Commands.draft(null, [ergoPath, ergoPath2, ctoPath], contractPath, '1970-01-01T00:00:00Z', null);
            result.response.should.equal('\nThis is a fixed interest loan to the amount of 100000.0\nat the yearly interest rate of 2.5%\nwith a loan term of 15,\nand monthly payments of {{667.0}}\n');
        });
        it('should generate text for a smart Ergo contract (wrap variable)', async function () {
            const ergoPath = Path.join('test/examples/interests', 'logic/logic.ergo');
            const ergoPath2 = Path.join('test/examples/interests', 'logic/interests.ergo');
            const ctoPath = Path.join('test/examples/interests', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/interests', 'data.json') };
            const result = await Commands.draft(null, [ergoPath, ergoPath2, ctoPath], contractPath, '1970-01-01T00:00:00Z', { wrapVariables: true });
            result.response.should.equal('\nThis is a fixed interest loan to the amount of <variable id="loanAmount" value="100000.0"/>\nat the yearly interest rate of <variable id="rate" value="2.5"/>%\nwith a loan term of <variable id="loanDuration" value="15"/>,\nand monthly payments of <computed value="667.0"/>\n');
        });
        it('should generate text for a late delivery and penalty contract (wrap variable)', async function () {
            const templatePath = Path.join('test/examples/latedeliveryandpenalty', 'grammar/template.tem.md');
            const ergoPath = Path.join('test/examples/latedeliveryandpenalty', 'logic/logic.ergo');
            const ctoPath = Path.join('test/examples/latedeliveryandpenalty', 'model/model.cto');
            const ctoPath2 = Path.join('test/examples/latedeliveryandpenalty', 'model/test.cto');
            const contractPath = { file: Path.join('test/examples/latedeliveryandpenalty', 'data.json') };
            const result = await Commands.draft(null, [ergoPath, templatePath, ctoPath2, ctoPath], contractPath, '1970-01-01T00:00:00Z', { wrapVariables: true });
            result.response.should.equal('Late Delivery and Penalty. In case of delayed delivery<variable id="forceMajeure" value="%20except%20for%20Force%20Majeure%20cases,"/> the Seller shall pay to the Buyer for every <variable id="penaltyDuration" value="2%20days"/> of delay penalty amounting to <variable id="penaltyPercentage" value="10.5"/>% of the total value of the Equipment whose delivery has been delayed. Any fractional part of a <variable id="fractionalPart" value="days"/> is to be considered a full <variable id="fractionalPart" value="days"/>. The total amount of penalty shall not however, exceed <variable id="capPercentage" value="55.0"/>% of the total value of the Equipment involved in late delivery. If the delay is more than <variable id="termination" value="15%20days"/>, the Buyer is entitled to terminate this Contract.');
        });
        it('should throw when smart Ergo clause without a cto', async function () {
            const ergoPath = Path.join('test/examples/interests', 'logic/logic.ergo');
            const ergoPath2 = Path.join('test/examples/interests', 'logic/interests.ergo');
            const contractPath = { file: Path.join('test/examples/interests', 'data.json') };
            return Commands.draft(null, [ergoPath, ergoPath2], contractPath, '1970-01-01T00:00:00Z', null).should.be.rejectedWith('Compilation error (at file test/examples/interests/logic/logic.ergo line 19 col 24). Cannot find type with name \'TemplateModel\'\ncontract Interests over TemplateModel {\n                        ^^^^^^^^^^^^^  ');
        });
        it('should fail when Ergo logic is missing', async function () {
            const ctoPath = Path.join('test/examples/interests', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/interests', 'data.json') };
            return Commands.draft(null, [ctoPath], contractPath, '1970-01-01T00:00:00Z', null).should.be.rejectedWith('No input ergo found');
        });
    });
    describe('#generatetextwithinterestsvar', function () {
        it('should generate text for a smart Ergo contract', async function () {
            const ergoPath = Path.join('test/examples/interestsvar', 'logic/logic.ergo');
            const ergoPath2 = Path.join('test/examples/interestsvar', 'logic/interests.ergo');
            const ctoPath = Path.join('test/examples/interestsvar', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/interestsvar', 'data.json') };
            const result = await Commands.draft(null, [ergoPath, ergoPath2, ctoPath], contractPath, '1970-01-01T00:00:00Z', null);
            result.response.should.equal('\nThis is a fixed interest loan to the amount of 100000.0\nat the yearly interest rate of 2.5%\nwith a loan term of 15,\nand monthly payments of {{667.0}}\n');
        });
        it('should throw when smart Ergo clause without a cto', async function () {
            const ergoPath = Path.join('test/examples/interestsvar', 'logic/logic.ergo');
            const ergoPath2 = Path.join('test/examples/interestsvar', 'logic/interests.ergo');
            const contractPath = { file: Path.join('test/examples/interestsvar', 'data.json') };
            return Commands.draft(null, [ergoPath, ergoPath2], contractPath, '1970-01-01T00:00:00Z', null).should.be.rejectedWith('Compilation error (at file test/examples/interestsvar/logic/logic.ergo line 19 col 24). Cannot find type with name \'TemplateModel\'\ncontract Interests over TemplateModel {\n                        ^^^^^^^^^^^^^  ');
        });
        it('should fail when Ergo logic is missing', async function () {
            const ctoPath = Path.join('test/examples/interestsvar', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/interestsvar', 'data.json') };
            return Commands.draft(null, [ctoPath], contractPath, '1970-01-01T00:00:00Z', null).should.be.rejectedWith('No input ergo found');
        });
        it('should initialize a smart Ergo contract state', async function () {
            const templatePath = Path.join('test/examples/interestsvar2', 'grammar/template.tem.md');
            const ergoPath = Path.join('test/examples/interestsvar2', 'logic/logic2.ergo');
            const ergoPath2 = Path.join('test/examples/interestsvar2', 'logic/interests.ergo');
            const ctoPath = Path.join('test/examples/interestsvar2', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/interestsvar2', 'data.json') };
            const result = await Commands.draft(null, [ergoPath, ergoPath2, ctoPath, templatePath], contractPath, '1970-01-01T00:00:00Z', null);
            result.response.should.equal('This is a fixed interest loan to the amount of 100000.0\nat the yearly interest rate of 2.5%\nwith a loan term of 15,\nand monthly payments of {{667.0}}\n');
        });
    });
    describe('#initinstallmentsale', function () {
        it('should invoke init', async function () {
            const ergoPath = Path.join('test/examples/installment-sale', 'logic/logic.ergo');
            const ctoPath = Path.join('test/examples/installment-sale', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/installment-sale', 'data.json') };
            const paramsPath = { file: Path.join('test/examples/installment-sale', 'params.json') };
            const result = await Commands.initialize(null, [ergoPath, ctoPath], contractPath, '1970-01-01T00:00:00Z', paramsPath);
            result.state.balance_remaining.should.equal(10000.00);
        });
        it('should throw when initializing a smart Ergo contract with an illegal model', async function () {
            const ergoPath = Path.join('test/examples/installment-sale', 'logic/logic.ergo');
            const ctoPath = Path.join('test/examples/installment-sale', 'model/modelErr.cto');
            const contractPath = { file: Path.join('test/examples/installment-sale', 'data.json') };
            const paramsPath = { file: Path.join('test/examples/installment-sale', 'params.json') };
            return Commands.initialize(null, [ergoPath, ctoPath], contractPath, '1970-01-01T00:00:00Z', paramsPath).should.be.rejectedWith('Expected "namespace", comment, end of line, or whitespace but "E" found. File test/examples/installment-sale/model/modelErr.cto line 15 column 1');
        });
        it('should throw when initializing a smart Ergo clause without a cto', async function () {
            const ergoPath = Path.join('test/examples/installment-sale', 'logic/logic.ergo');
            const contractPath = { file: Path.join('test/examples/installment-sale', 'data.json') };
            const paramsPath = { file: Path.join('test/examples/installment-sale', 'params.json') };
            return Commands.initialize(null, [ergoPath], contractPath, '1970-01-01T00:00:00Z', paramsPath).should.be.rejectedWith('Compilation error (at file test/examples/installment-sale/logic/logic.ergo line 19 col 30). Cannot find type with name \'TemplateModel\'\ncontract InstallmentSale over TemplateModel state InstallmentSaleState {\n                              ^^^^^^^^^^^^^                             ');
        });
        it('should fail when Ergo logic is missing', async function () {
            const ctoPath = Path.join('test/examples/installment-sale', 'model/model.cto');
            const contractPath = { file: Path.join('test/examples/installment-sale', 'data.json') };
            const paramsPath = { file: Path.join('test/examples/installment-sale', 'params.json') };
            return Commands.initialize(null, [ctoPath], contractPath, '1970-01-01T00:00:00Z', paramsPath).should.be.rejectedWith('No input ergo found');
        });
    });
    describe('#parsectotofile', function () {
        it('should parse CTO to CTOJ', async function () {
            const ctoPath = Path.join('test/examples/helloworld', 'model/model.cto');
            const result = await Commands.parseCTOtoFile(ctoPath);
            result.should.not.be.null;
        });
    });
});
