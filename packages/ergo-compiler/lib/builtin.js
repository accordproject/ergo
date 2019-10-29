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

const { ContractModel } = require('./externalModels/ContractModel');
const { RuntimeModel } = require('./externalModels/RuntimeModel');
const { MoneyModel } = require('./externalModels/MoneyModel');
const { TimeModel } = require('./externalModels/TimeModel');

const SystemModel = `namespace org.accordproject.base
abstract asset Asset {  }
abstract participant Participant {  }
abstract transaction Transaction identified by transactionId {
  o String transactionId
}
abstract event Event identified by eventId {
  o String eventId
}`;

module.exports = { SystemModel, ContractModel, RuntimeModel, MoneyModel, TimeModel };
