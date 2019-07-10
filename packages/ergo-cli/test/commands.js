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
            const ergoPath = Path.join('test/examples/helloworld', 'logic.ergo');
            const ctoPath = Path.join('test/examples/helloworld', 'model.cto');
            const contractPath = { file: Path.join('test/examples/helloworld', 'contract.json') };
            const requestPath = { file: Path.join('test/examples/helloworld', 'request.json') };
            const statePath = { file: Path.join('test/examples/helloworld', 'state.json') };
            const result = await Commands.execute([ergoPath], [ctoPath], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]);
            result.response.output.should.equal('Hello Fred Blogs (Accord Project)');
        });
        it('should throw when executing a request to a smart Ergo contract with an illegal model', async function () {
            const ergoPath = Path.join('test/examples/helloworld', 'logic.ergo');
            const ctoPath = Path.join('test/examples/helloworld', 'modelErr.cto');
            const contractPath = { file: Path.join('test/examples/helloworld', 'contract.json') };
            const requestPath = { file: Path.join('test/examples/helloworld', 'request.json') };
            const statePath = { file: Path.join('test/examples/helloworld', 'state.json') };
            return Commands.execute([ergoPath], [ctoPath], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]).should.be.rejectedWith('Expected "namespace", comment, end of line, or whitespace but "E" found. File test/examples/helloworld/modelErr.cto line 15 column 1');
        });
        it('should throw when executing a request to a smart Ergo contract without its cto', async function () {
            const ergoPath = Path.join('test/examples/helloworld', 'logic.ergo');
            const contractPath = { file: Path.join('test/examples/helloworld', 'contract.json') };
            const requestPath = { file: Path.join('test/examples/helloworld', 'request.json') };
            const statePath = { file: Path.join('test/examples/helloworld', 'state.json') };
            return Commands.execute([ergoPath], undefined, contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]).should.be.rejectedWith('Compilation error (at file test/examples/helloworld/logic.ergo line 17 col 25). Cannot find type with name \'TemplateModel\'\ncontract HelloWorld over TemplateModel {\n                         ^^^^^^^^^^^^^  ');
        });
        it('should fail when Ergo logic is missing', async function () {
            const ctoPath = Path.join('test/examples/helloworld', 'model.cto');
            const contractPath = { file: Path.join('test/examples/helloworld', 'contract.json') };
            const requestPath = { file: Path.join('test/examples/helloworld', 'request.json') };
            const statePath = { file: Path.join('test/examples/helloworld', 'state.json') };
            return Commands.execute(undefined, [ctoPath], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]).should.be.rejectedWith('No input ergo found');
        });
    });
    describe('#executehellostate', function () {
        it('should execute a smart Ergo contract with state once', async function () {
            const ergoPath = Path.join('test/examples/helloworldstate', 'logic.ergo');
            const ctoPath = Path.join('test/examples/helloworldstate', 'model.cto');
            const contractPath = { file: Path.join('test/examples/helloworldstate', 'contract.json') };
            const requestPath = { file: Path.join('test/examples/helloworldstate', 'request.json') };
            const statePath = { file: Path.join('test/examples/helloworldstate', 'state.json') };
            const result = await Commands.execute([ergoPath], [ctoPath], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]);
            result.response.output.should.equal('Hello Fred Blogs (Accord Project) (1.0)');
        });
        it('should execute a smart Ergo contract with state thrice', async function () {
            const ergoPath = Path.join('test/examples/helloworldstate', 'logic.ergo');
            const ctoPath = Path.join('test/examples/helloworldstate', 'model.cto');
            const contractPath = { file: Path.join('test/examples/helloworldstate', 'contract.json') };
            const requestPath = { file: Path.join('test/examples/helloworldstate', 'request.json') };
            const statePath = { file: Path.join('test/examples/helloworldstate', 'state.json') };
            const result = await Commands.execute([ergoPath], [ctoPath], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath,requestPath,requestPath]);
            result.response.output.should.equal('Hello Fred Blogs (Accord Project) (3.0)');
        });
    });
    describe('#executeinstallmentsale', function () {
        it('should initialize a smart Ergo contract state', async function () {
            const ergoPath = Path.join('test/examples/installment-sale', 'logic.ergo');
            const ctoPath = Path.join('test/examples/installment-sale', 'model.cto');
            const contractPath = { file: Path.join('test/examples/installment-sale', 'contract.json') };
            const result = await Commands.execute([ergoPath], [ctoPath], contractPath, null, '1970-01-01T00:00:00Z', []);
            result.state.balance_remaining.should.equal(10000.00);
        });
        it('should initialize a smart Ergo contract and execute one request', async function () {
            const ergoPath = Path.join('test/examples/installment-sale', 'logic.ergo');
            const ctoPath = Path.join('test/examples/installment-sale', 'model.cto');
            const contractPath = { file: Path.join('test/examples/installment-sale', 'contract.json') };
            const requestPath = { file: Path.join('test/examples/installment-sale', 'request.json') };
            const result = await Commands.execute([ergoPath], [ctoPath], contractPath, null, '1970-01-01T00:00:00Z', [requestPath]);
            result.state.balance_remaining.should.equal(7612.499999999999);
        });
    });
    describe('#executepromissorynote', function () {
        it('should execute a smart Ergo contract', async function () {
            const ergoPath = Path.join('test/examples/promissory-note', 'logic.ergo');
            const ctoPath1 = Path.join('test/examples/promissory-note', 'business.cto');
            const ctoPath2 = Path.join('test/examples/promissory-note', 'model.cto');
            const contractPath = { file: Path.join('test/examples/promissory-note', 'contract.json')};
            const requestPath = { file: Path.join('test/examples/promissory-note', 'request.json') };
            const statePath = { file: Path.join('test/examples/promissory-note', 'state.json') };
            const result = await Commands.execute([ergoPath], [ctoPath1, ctoPath2], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]);
            result.response.outstandingBalance.should.equal(1425.4396822450633);
        });
    });
    describe('#executepromissorynotemodule', function () {
        it('should execute a smart Ergo contract with two modules', async function () {
            const ergoPath1 = Path.join('test/examples/promissory-note', 'money.ergo');
            const ergoPath2 = Path.join('test/examples/promissory-note', 'logic3.ergo');
            const ctoPath1 = Path.join('test/examples/promissory-note', 'business.cto');
            const ctoPath2 = Path.join('test/examples/promissory-note', 'model.cto');
            const contractPath = { file: Path.join('test/examples/promissory-note', 'contract.json')};
            const requestPath = { file: Path.join('test/examples/promissory-note', 'request.json') };
            const statePath = { file: Path.join('test/examples/promissory-note', 'state.json') };
            const result = await Commands.execute([ergoPath1, ergoPath2], [ctoPath1, ctoPath2], contractPath, statePath, '1970-01-01T00:00:00Z', [requestPath]);
            result.response.outstandingBalance.should.equal(1425.4396822450633);
        });
    });
    describe('#executeacceptanceofdelivery', function () {
        it('should execute a smart Ergo contract', async function () {
            const ergoPath = Path.join('test/examples/acceptance-of-delivery', 'logic.ergo');
            const ctoPath = Path.join('test/examples/acceptance-of-delivery', 'model.cto');
            const contractPath = { file: Path.join('test/examples/acceptance-of-delivery', 'contract.json') };
            const requestPath = { file: Path.join('test/examples/acceptance-of-delivery', 'request.json') };
            const statePath = { file: Path.join('test/examples/acceptance-of-delivery', 'state.json') };
            const result = await Commands.execute([ergoPath], [ctoPath], contractPath, statePath, '2019-01-20T16:34:00-05:00', [requestPath]);
            result.response.status.should.equal('OUTSIDE_INSPECTION_PERIOD');
        });
        it('should execute a smart Ergo contract', async function () {
            const ergoPath = Path.join('test/examples/acceptance-of-delivery', 'logic.ergo');
            const ctoPath = Path.join('test/examples/acceptance-of-delivery', 'model.cto');
            const contractPath = { file: Path.join('test/examples/acceptance-of-delivery', 'contract.json') };
            const requestPath = { file: Path.join('test/examples/acceptance-of-delivery', 'request.json') };
            const statePath = { file: Path.join('test/examples/acceptance-of-delivery', 'state.json') };
            const result = await Commands.execute([ergoPath], [ctoPath], contractPath, statePath, '2019-01-11T16:34:00-05:00', [requestPath]);
            result.response.status.should.equal('PASSED_TESTING');
        });
    });
    describe('#invokehelloworld', function () {
        it('should invoke a clause in a smart Ergo contract', async function () {
            const ergoPath = Path.join('test/examples/helloworld', 'logic4.ergo');
            const ctoPath = Path.join('test/examples/helloworld', 'model.cto');
            const contractPath = { file: Path.join('test/examples/helloworld', 'contract.json') };
            const paramsPath = { file: Path.join('test/examples/helloworld', 'params.json') };
            const statePath = { file: Path.join('test/examples/helloworld', 'state.json') };
            const result = await Commands.invoke([ergoPath], [ctoPath], 'helloworld', contractPath, statePath, '1970-01-01T00:00:00Z', paramsPath, null);
            result.response.output.should.equal('Bonjour, Fred Blogs (Accord Project)');
        });
        it('should throw when invoking a clause in a smart Ergo contract with an illegal model', async function () {
            const ergoPath = Path.join('test/examples/helloworld', 'logic.ergo');
            const ctoPath = Path.join('test/examples/helloworld', 'modelErr.cto');
            const contractPath = { file: Path.join('test/examples/helloworld', 'contract.json') };
            const paramsPath = { file: Path.join('test/examples/helloworld', 'params.json') };
            const statePath = { file: Path.join('test/examples/helloworld', 'state.json') };
            return Commands.invoke([ergoPath], [ctoPath], 'helloworld', contractPath, statePath, '1970-01-01T00:00:00Z', paramsPath).should.be.rejectedWith('Expected "namespace", comment, end of line, or whitespace but "E" found. File test/examples/helloworld/modelErr.cto line 15 column 1');
        });
        it('should invoke a clause in a smart Ergo contract (JSON parameters)', async function () {
            const ergoPath = Path.join('test/examples/helloworld', 'logic4.ergo');
            const ctoPath = Path.join('test/examples/helloworld', 'model.cto');
            const contractPath = { file: Path.join('test/examples/helloworld', 'contract.json') };
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
            const result = await Commands.invoke([ergoPath], [ctoPath], 'helloworld', contractPath, statePath, '1970-01-01T00:00:00Z', paramsJson, null);
            result.response.output.should.equal('Bonjour, Fred Blogs (Accord Project)');
        });
        it('should throw when smart Ergo clause without a cto', async function () {
            const ergoPath = Path.join('test/examples/helloworld', 'logic4.ergo');
            const contractPath = { file: Path.join('test/examples/helloworld', 'contract.json') };
            const paramsPath = { file: Path.join('test/examples/helloworld', 'params.json') };
            const statePath = { file: Path.join('test/examples/helloworld', 'state.json') };
            return Commands.invoke([ergoPath], undefined, 'helloworld', contractPath, statePath, '1970-01-01T00:00:00Z', paramsPath).should.be.rejectedWith('Compilation error (at file test/examples/helloworld/logic4.ergo line 17 col 25). Cannot find type with name \'TemplateModel\'\ncontract HelloWorld over TemplateModel {\n                         ^^^^^^^^^^^^^  ');
        });
        it('should fail when Ergo logic is missing', async function () {
            const ctoPath = Path.join('test/examples/helloworld', 'model.cto');
            const contractPath = { file: Path.join('test/examples/helloworld', 'contract.json') };
            const paramsPath = { file: Path.join('test/examples/helloworld', 'params.json') };
            const statePath = { file: Path.join('test/examples/helloworld', 'state.json') };
            return Commands.invoke(undefined, [ctoPath], 'helloworld', contractPath, statePath, '1970-01-01T00:00:00Z', paramsPath, null).should.be.rejectedWith('No input ergo found');
        });
    });
    describe('#generatetext', function () {
        it('should generate text for a smart Ergo contract', async function () {
            const ergoPath = Path.join('test/examples/interests', 'logic.ergo');
            const ergoPath2 = Path.join('test/examples/interests', 'interests.ergo');
            const ctoPath = Path.join('test/examples/interests', 'model.cto');
            const contractPath = { file: Path.join('test/examples/interests', 'contract.json') };
            const result = await Commands.generateText([ergoPath,ergoPath2], [ctoPath], contractPath, '1970-01-01T00:00:00Z', null, null);
            result.response.should.equal('\nThis is a fixed interest loan to the amount of 100000.0\nat the yearly interest rate of 2.5%\nwith a loan term of 15,\nand monthly payments of {{667.0}}\n');
        });
        it('should generate text for a smart Ergo contract (wrap variable)', async function () {
            const ergoPath = Path.join('test/examples/interests', 'logic.ergo');
            const ergoPath2 = Path.join('test/examples/interests', 'interests.ergo');
            const ctoPath = Path.join('test/examples/interests', 'model.cto');
            const contractPath = { file: Path.join('test/examples/interests', 'contract.json') };
            const result = await Commands.generateText([ergoPath,ergoPath2], [ctoPath], contractPath, '1970-01-01T00:00:00Z', null, { wrapVariables: true });
            result.response.should.equal('\nThis is a fixed interest loan to the amount of <variable id="loanAmount" value="100000.0"/>\nat the yearly interest rate of <variable id="rate" value="2.5"/>%\nwith a loan term of <variable id="loanDuration" value="15"/>,\nand monthly payments of <computed value="667.0"/>\n');
        });
        it('should generate text for a late delivery and penalty contract (wrap variable)', async function () {
            const templatePath = { file: Path.join('test/examples/latedeliveryandpenalty', 'template.tem') };
            const ergoPath = Path.join('test/examples/latedeliveryandpenalty', 'logic.ergo');
            const ctoPath = Path.join('test/examples/latedeliveryandpenalty', 'model.cto');
            const ctoPath2 = Path.join('test/examples/latedeliveryandpenalty', 'test.cto');
            const contractPath = { file: Path.join('test/examples/latedeliveryandpenalty', 'contract.json') };
            const result = await Commands.generateText([ergoPath], [ctoPath2,ctoPath], contractPath, '1970-01-01T00:00:00Z', templatePath, { wrapVariables: true });
            result.response.should.equal('Late Delivery and Penalty. In case of delayed delivery<variable id="forceMajeure" value="%20except%20for%20Force%20Majeure%20cases,"/> the Seller shall pay to the Buyer for every <variable id="penaltyDuration" value="2%20days"/> of delay penalty amounting to <variable id="penaltyPercentage" value="10.5"/>% of the total value of the Equipment whose delivery has been delayed. Any fractional part of a <variable id="fractionalPart" value="days"/> is to be considered a full <variable id="fractionalPart" value="days"/>. The total amount of penalty shall not however, exceed <variable id="capPercentage" value="55.0"/>% of the total value of the Equipment involved in late delivery. If the delay is more than <variable id="termination" value="15%20days"/>, the Buyer is entitled to terminate this Contract.');
        });
        it('should throw when smart Ergo clause without a cto', async function () {
            const ergoPath = Path.join('test/examples/interests', 'logic.ergo');
            const ergoPath2 = Path.join('test/examples/interests', 'interests.ergo');
            const contractPath = { file: Path.join('test/examples/interests', 'contract.json') };
            return Commands.generateText([ergoPath,ergoPath2], undefined, contractPath, '1970-01-01T00:00:00Z', null, null).should.be.rejectedWith('Compilation error (at file test/examples/interests/logic.ergo line 20 col 24). Cannot find type with name \'TemplateModel\'\ncontract Interests over TemplateModel {\n                        ^^^^^^^^^^^^^  ');
        });
        it('should fail when Ergo logic is missing', async function () {
            const ctoPath = Path.join('test/examples/interests', 'model.cto');
            const contractPath = { file: Path.join('test/examples/interests', 'contract.json') };
            return Commands.generateText(undefined, [ctoPath], contractPath, '1970-01-01T00:00:00Z', null, null).should.be.rejectedWith('No input ergo found');
        });
    });
    describe('#generatetextwithinterestsvar', function () {
        it('should generate text for a smart Ergo contract', async function () {
            const ergoPath = Path.join('test/examples/interestsvar', 'logic.ergo');
            const ergoPath2 = Path.join('test/examples/interestsvar', 'interests.ergo');
            const ctoPath = Path.join('test/examples/interestsvar', 'model.cto');
            const contractPath = { file: Path.join('test/examples/interestsvar', 'contract.json') };
            const result = await Commands.generateText([ergoPath,ergoPath2], [ctoPath], contractPath, '1970-01-01T00:00:00Z', null, null);
            result.response.should.equal('\nThis is a fixed interest loan to the amount of 100000.0\nat the yearly interest rate of 2.5%\nwith a loan term of 15,\nand monthly payments of {{667.0}}\n');
        });
        it('should throw when smart Ergo clause without a cto', async function () {
            const ergoPath = Path.join('test/examples/interestsvar', 'logic.ergo');
            const ergoPath2 = Path.join('test/examples/interestsvar', 'interests.ergo');
            const contractPath = { file: Path.join('test/examples/interestsvar', 'contract.json') };
            return Commands.generateText([ergoPath,ergoPath2], undefined, contractPath, '1970-01-01T00:00:00Z', null, null).should.be.rejectedWith('Compilation error (at file test/examples/interestsvar/logic.ergo line 20 col 24). Cannot find type with name \'TemplateModel\'\ncontract Interests over TemplateModel {\n                        ^^^^^^^^^^^^^  ');
        });
        it('should fail when Ergo logic is missing', async function () {
            const ctoPath = Path.join('test/examples/interestsvar', 'model.cto');
            const contractPath = { file: Path.join('test/examples/interestsvar', 'contract.json') };
            return Commands.generateText(undefined, [ctoPath], contractPath, '1970-01-01T00:00:00Z', null, null).should.be.rejectedWith('No input ergo found');
        });
        it('should initialize a smart Ergo contract state', async function () {
            const templatePath = { file: Path.join('test/examples/interestsvar', 'logic2.tem') };
            const ergoPath = Path.join('test/examples/interestsvar', 'logic2.ergo');
            const ergoPath2 = Path.join('test/examples/interestsvar', 'interests.ergo');
            const ctoPath = Path.join('test/examples/interestsvar', 'model.cto');
            const contractPath = { file: Path.join('test/examples/interestsvar', 'contract.json') };
            const result = await Commands.generateText([ergoPath,ergoPath2], [ctoPath], contractPath, '1970-01-01T00:00:00Z', templatePath, null);
            result.response.should.equal('This is a fixed interest loan to the amount of 100000.0\nat the yearly interest rate of 2.5%\nwith a loan term of 15,\nand monthly payments of {{667.0}}\n');
        });
        it('should initialize a smart Ergo contract state (template content)', async function () {
            const templateContent = {
                name: 'foo.tem',
                content: `This is a fixed interest loan to the amount of {[loanAmount]}
at the yearly interest rate of {[rate]}%
with a loan term of {[loanDuration]},
and monthly payments of {{monthlyPaymentFormula(contract.loanAmount,contract.rate,contract.loanDuration)}}
`
            };
            const ergoPath = Path.join('test/examples/interestsvar', 'logic2.ergo');
            const ergoPath2 = Path.join('test/examples/interestsvar', 'interests.ergo');
            const ctoPath = Path.join('test/examples/interestsvar', 'model.cto');
            const contractPath = { file: Path.join('test/examples/interestsvar', 'contract.json') };
            const result = await Commands.generateText([ergoPath,ergoPath2], [ctoPath], contractPath, '1970-01-01T00:00:00Z', templateContent, null);
            result.response.should.equal('This is a fixed interest loan to the amount of 100000.0\nat the yearly interest rate of 2.5%\nwith a loan term of 15,\nand monthly payments of {{667.0}}\n');
        });
    });
    describe('#initinstallmentsale', function () {
        it('should invoke init', async function () {
            const ergoPath = Path.join('test/examples/installment-sale', 'logic.ergo');
            const ctoPath = Path.join('test/examples/installment-sale', 'model.cto');
            const contractPath = { file: Path.join('test/examples/installment-sale', 'contract.json') };
            const paramsPath = { file: Path.join('test/examples/installment-sale', 'params.json') };
            const result = await Commands.init([ergoPath], [ctoPath], contractPath, '1970-01-01T00:00:00Z', paramsPath);
            result.state.balance_remaining.should.equal(10000.00);
        });
        it('should throw when initializing a smart Ergo contract with an illegal model', async function () {
            const ergoPath = Path.join('test/examples/installment-sale', 'logic.ergo');
            const ctoPath = Path.join('test/examples/installment-sale', 'modelErr.cto');
            const contractPath = { file: Path.join('test/examples/installment-sale', 'contract.json') };
            const paramsPath = { file: Path.join('test/examples/installment-sale', 'params.json') };
            return Commands.init([ergoPath], [ctoPath], contractPath, '1970-01-01T00:00:00Z', paramsPath).should.be.rejectedWith('Expected "namespace", comment, end of line, or whitespace but "E" found. File test/examples/installment-sale/modelErr.cto line 15 column 1');
        });
        it('should throw when initializing a smart Ergo clause without a cto', async function () {
            const ergoPath = Path.join('test/examples/installment-sale', 'logic.ergo');
            const contractPath = { file: Path.join('test/examples/installment-sale', 'contract.json') };
            const paramsPath = { file: Path.join('test/examples/installment-sale', 'params.json') };
            return Commands.init([ergoPath], undefined, contractPath, '1970-01-01T00:00:00Z', paramsPath).should.be.rejectedWith('Compilation error (at file test/examples/installment-sale/logic.ergo line 19 col 30). Cannot find type with name \'TemplateModel\'\ncontract InstallmentSale over TemplateModel state InstallmentSaleState {\n                              ^^^^^^^^^^^^^                             ');
        });
        it('should fail when Ergo logic is missing', async function () {
            const ctoPath = Path.join('test/examples/installment-sale', 'model.cto');
            const contractPath = { file: Path.join('test/examples/installment-sale', 'contract.json') };
            const paramsPath = { file: Path.join('test/examples/installment-sale', 'params.json') };
            return Commands.init(undefined, [ctoPath], contractPath, '1970-01-01T00:00:00Z', paramsPath).should.be.rejectedWith('No input ergo found');
        });
    });
    describe('#parsectotofile', function () {
        it('should parse CTO to CTOJ', async function () {
            const ctoPath = Path.join('test/examples/helloworld', 'model.cto');
            const result = await Commands.parseCTOtoFile(ctoPath);
            result.should.not.be.null;
        });
    });
});
