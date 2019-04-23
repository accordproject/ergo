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

const contractModel = `namespace org.accordproject.cicero.contract

/**
 * Contract Data
 * -- Describes the structure of contracts and clauses
 */

/* A contract state is an asset -- The runtime state of the contract */
asset AccordContractState identified by stateId {
  o String stateId
}

/* A party to a contract */
participant AccordParty identified by partyId {
  o String partyId
}

/* A contract is a asset -- This contains the contract data */
abstract asset AccordContract identified by contractId {
  o String contractId
  --> AccordParty[] parties optional
}

/* A clause is an asset -- This contains the clause data */
abstract asset AccordClause identified by clauseId {
  o String clauseId
}
`;
const runtimeModel = `namespace org.accordproject.cicero.runtime

import org.accordproject.cicero.contract.AccordContract
import org.accordproject.cicero.contract.AccordContractState
import org.accordproject.money.MonetaryAmount

/**
 * Contract API
 * -- Describes input and output of calls to a contract's clause
 */

/* A request is a transaction */
transaction Request {}

/* A response is a transaction */
transaction Response {}

/* An Error is a transaction */
abstract transaction ErrorResponse {}

/* An event that represents an obligation that needs to be fulfilled */
abstract event Obligation {
  /* A back reference to the governing contract that emitted this obligation */
  --> AccordContract contract

  /* The party that is obligated */
  --> Participant promisor optional // TODO make this mandatory once proper party support is in place

  /* The party that receives the performance */
  --> Participant promisee optional // TODO make this mandatory once proper party support is in place

  /* The time before which the obligation is fulfilled */
  o DateTime deadline optional
}

event PaymentObligation extends Obligation{
  o MonetaryAmount amount
  o String description
}

event NotificationObligation extends Obligation {
  o String title
  o String message
}

/* A payload has contract data, a request and a state */
concept Payload {
  o AccordContract contract  // the contract data
  o Request request
  o AccordContractState state optional
}

/* If the call to a contract's clause succeeds, it returns a response, a list of events and a new state */
concept Success {
  o Response response
  o AccordContractState state
  o Event[] emit
}
/* If the call to a contract's clause fails, it returns and error */ 
concept Failure {
  o ErrorResponse error
}

/**
 * The functional signature for a contract call is as follows:
 * clausecall : String contractName -> String clauseName -> Payload payload -> Success | Failure
 */
`;
const moneyModel = `namespace org.accordproject.money

/**
 * Represents an amount of Cryptocurrency
 */
concept CryptoMonetaryAmount {
  o Double doubleValue
  o CryptoCurrencyCode cryptoCurrencyCode
}

/**
 * Cyptocurrency codes. From https://en.wikipedia.org/wiki/List_of_cryptocurrencies
 */
enum CryptoCurrencyCode {
  o ADA
  o BCH
  o BTC
  o DASH
  o EOS
  o ETC
  o ETH
  o LTC
  o NEO
  o XLM
  o XMR
  o XRP
  o ZEC
}

/**
 * Represents an amount of money
 */
concept MonetaryAmount {
  o Double doubleValue // convert to fixed-point?
  o CurrencyCode currencyCode
}

/**
 * ISO 4217 codes. From https://en.wikipedia.org/wiki/ISO_4217
 * https://www.currency-iso.org/en/home/tables/table-a1.html
 */
enum CurrencyCode {
o AED
o AFN
o ALL
o AMD
o ANG
o AOA
o ARS
o AUD
o AWG
o AZN
o BAM
o BBD
o BDT
o BGN
o BHD
o BIF
o BMD
o BND
o BOB
o BOV
o BRL
o BSD
o BTN
o BWP
o BYN
o BZD
o CAD
o CDF
o CHE
o CHF
o CHW
o CLF
o CLP
o CNY
o COP
o COU
o CRC
o CUC
o CUP
o CVE
o CZK
o DJF
o DKK
o DOP
o DZD
o EGP
o ERN
o ETB
o EUR
o FJD
o FKP
o GBP
o GEL
o GHS
o GIP
o GMD
o GNF
o GTQ
o GYD
o HKD
o HNL
o HRK
o HTG
o HUF
o IDR
o ILS
o INR
o IQD
o IRR
o ISK
o JMD
o JOD
o JPY
o KES
o KGS
o KHR
o KMF
o KPW
o KRW
o KWD
o KYD
o KZT
o LAK
o LBP
o LKR
o LRD
o LSL
o LYD
o MAD
o MDL
o MGA
o MKD
o MMK
o MNT
o MOP
o MRU
o MUR
o MVR
o MWK
o MXN
o MXV
o MYR
o MZN
o NAD
o NGN
o NIO
o NOK
o NPR
o NZD
o OMR
o PAB
o PEN
o PGK
o PHP
o PKR
o PLN
o PYG
o QAR
o RON
o RSD
o RUB
o RWF
o SAR
o SBD
o SCR
o SDG
o SEK
o SGD
o SHP
o SLL
o SOS
o SRD
o SSP
o STN
o SVC
o SYP
o SZL
o THB
o TJS
o TMT
o TND
o TOP
o TRY
o TTD
o TWD
o TZS
o UAH
o UGX
o USD
o USN
o UYI
o UYU
o UZS
o VEF
o VND
o VUV
o WST
o XAF
o XAG
o XAU
o XBA
o XBB
o XBC
o XBD
o XCD
o XDR
o XOF
o XPD
o XPF
o XPT
o XSU
o XTS
o XUA
o XXX
o YER
o ZAR
o ZMW
o ZWL
}

`;
const timeModel = `namespace org.accordproject.time

/**
 * Units for a duration.
 */
enum TemporalUnit {
  o seconds
  o minutes
  o hours
  o days
  o weeks
}

/**
 * A duration. For example, 6 hours.
 */
concept Duration {
  o Long amount
  o TemporalUnit unit
}

/**
 * Units for a time period.
 */
enum PeriodUnit {
  o days
  o weeks
  o months
  o quarters
  o years
}

/**
 * A time period. For example, 2 months.
 */
concept Period {
  o Long amount
  o PeriodUnit unit
}
`;
const markdownModel = `
namespace org.accordproject.markdown

concept MarkdownOptions {
  o Boolean markdown
  o Boolean wrapVariables
}
`;

module.exports = { contractModel, runtimeModel, moneyModel, timeModel, markdownModel };
