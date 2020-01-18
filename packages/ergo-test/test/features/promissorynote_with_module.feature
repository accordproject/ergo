Feature: Promissory note Contract
  This describes the expected behavior for the Accord Project's Promissory note contract, implemented with a separate Ergo module

  Background:
    Given the Ergo contract "org.accordproject.promissorynote.PromissoryNote" in file "../../../tests/promissory-note/logic/logic3.ergo"
    And the Ergo logic in file "../../../tests/promissory-note/logic/money.ergo"
    And the model in file "../../../tests/promissory-note/model/business.cto"
    And the model in file "../../../tests/promissory-note/model/model.cto"
    And the contract data
"""
{
  "$class": "org.accordproject.promissorynote.PromissoryNoteContract",
  "contractId": "71b1ebee-6b92-4bc5-bf79-29cde51d8494",
  "amount": {
    "$class": "org.accordproject.money.MonetaryAmount",
    "doubleValue": 1000,
    "currencyCode": "USD"
  },
  "date": "2018-01-30",
  "maker": "Daniel Selman",
  "interestRate": 3.8,
  "individual": true,
  "makerAddress": "1 Main Street",
  "lender": "Clause",
  "legalEntity": "CORP",
  "lenderAddress": "246 5th Ave, 3rd Fl, New York, NY 10001",
  "principal": 500,
  "maturityDate": "2019-01-20",
  "defaultDays": 90,
  "insolvencyDays": 90,
  "jurisdiction": "New York, NY"
}
"""

  Scenario: The contract gets initialized
    Then the initial state should be the default state

  Scenario: The contract should return the outstanding balance when a payment is made
    When it receives the request
"""
{
  "$class": "org.accordproject.promissorynote.Payment",
  "amountPaid": { "doubleValue" : 100.0, "currencyCode" : "USD" }
}
"""
    Then it should respond with
"""
{
  "outstandingBalance": 1425.4396822450633,
  "$class": "org.accordproject.promissorynote.Result"
}
"""
