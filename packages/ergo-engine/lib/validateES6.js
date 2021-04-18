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

const Factory = require('@accordproject/concerto-core').Factory;
const Serializer = require('@accordproject/concerto-core').Serializer;
const ResourceValidator = require('@accordproject/concerto-core/lib/serializer/resourcevalidator');

/**
 * Validate contract JSON
 * @param {object} modelManager - the Concerto model manager
 * @param {object} contract - the contract JSON
 * @param {number} utcOffset - UTC Offset for DateTime values
 * @param {object} options - parameters for contract variables validation
 * @return {object} the validated contract
 */
function validateContract(modelManager, contract, utcOffset, options) {
    options = options || {};

    const factory = new Factory(modelManager);
    const serializer = new Serializer(factory, modelManager);

    if (contract === null) { return null; }

    // ensure the contract is valid
    const validContract = serializer.fromJSON(contract, {validate: false, acceptResourcesForRelationships: true, utcOffset});
    validContract.$validator = new ResourceValidator({permitResourcesForRelationships: true});
    validContract.validate();
    const vJson = serializer.toJSON(validContract, Object.assign(options, {ergo:true,permitResourcesForRelationships:true}));
    return { serialized: vJson, validated: validContract };
}

/**
 * Validate input JSON
 * @param {object} modelManager - the Concerto model manager
 * @param {object} input - the input JSON
 * @param {number} utcOffset - UTC Offset for DateTime values
 * @return {object} the validated input
 */
function validateInput(modelManager, input, utcOffset) {
    const factory = new Factory(modelManager);
    const serializer = new Serializer(factory, modelManager);

    if (input === null) { return null; }

    // ensure the input is valid
    const validInput = serializer.fromJSON(input, {validate: false, acceptResourcesForRelationships: true, utcOffset});
    validInput.$validator = new ResourceValidator({permitResourcesForRelationships: true});
    validInput.validate();
    const vJson = serializer.toJSON(validInput, {ergo:true,permitResourcesForRelationships:true, utcOffset});
    return vJson;
}

/**
 * Validate input JSON record
 * @param {object} modelManager - the Concerto model manager
 * @param {object} input - the input JSON record
 * @param {number} utcOffset - UTC Offset for DateTime values
 * @return {object} the validated input
 */
function validateInputRecord(modelManager, input, utcOffset) {
    let validRecord = {};
    for(const key in input) {
        if (input[key] instanceof Object) {
            validRecord[key] = validateInput(modelManager, input[key], utcOffset);
        } else {
            validRecord[key] = input[key];
        }
    }
    return validRecord;
}

/**
 * Validate output JSON
 * @param {object} modelManager - the Concerto model manager
 * @param {object} output - the output JSON
 * @param {number} utcOffset - UTC Offset for DateTime values
 * @return {object} the validated output
 */
function validateOutput(modelManager, output, utcOffset) {
    const factory = new Factory(modelManager);
    const serializer = new Serializer(factory, modelManager);

    if (output === null) { return null; }

    if (output instanceof Object) {
        const vJson = output;
        const validOutput = serializer.fromJSON(vJson, {ergo: true, validate: false, acceptResourcesForRelationships: true, utcOffset});
        validOutput.$validator = new ResourceValidator({permitResourcesForRelationships: true});
        validOutput.validate();
        return serializer.toJSON(validOutput, {convertResourcesToRelationships: true, utcOffset});
    } else {
        return output;
    }
}

/**
 * Validate output JSON array
 * @param {object} modelManager - the Concerto model manager
 * @param {*} output - the output JSON array
 * @param {number} utcOffset - UTC Offset for DateTime values
 * @return {Array<object>} the validated output array
 */
function validateOutputArray(modelManager, output, utcOffset) {
    const outputArray = output.$coll.slice(0,output.$length);
    let resultArray = [];
    for (let i = 0; i < outputArray.length; i++) {
        resultArray.push(validateOutput(modelManager, outputArray[i], utcOffset));
    }
    return resultArray;
}

module.exports = {
    validateContract,
    validateInput,
    validateInputRecord,
    validateOutput,
    validateOutputArray,
};
