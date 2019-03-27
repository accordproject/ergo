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

/* eslint-disable no-unused-vars */
/* eslint-disable no-undef */
/* eslint-disable no-var */

/**
 * Execute the smart clause
 * @param {Context} context - the Accord context
 * @param {org.accordproject.copyrightlicense.PaymentRequest} context.request - the incoming request
 * @param {org.accordproject.copyrightlicense.PayOut} context.response - the response
 * @param {Event} context.emit - the emitted events
 */
function paymentClause(context) {
    var req = context.request;
    var res = context.response;
    var contract = context.contract;
    res.amount = contract.amount;
}
function __dispatch(context) {
    paymentClause(context);
}

/* eslint-enable no-unused-vars */
/* eslint-enable no-undef */
