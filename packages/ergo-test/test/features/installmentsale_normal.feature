Feature: Installment sale Contract
  This describes the expected behavior for the Accord Project's Installment sale contract

  Background:
    Given the Ergo contract "org.accordproject.installmentsale.InstallmentSale" in file "../../../tests/installment-sale/logic/logic.ergo"
    And the model in file "../../../tests/installment-sale/model/model.cto"
    And the contract data
"""
{
  "$class": "org.accordproject.installmentsale.TemplateModel",
  "BUYER": "Dan",
  "SELLER": "Ned",
  "INITIAL_DUE": 10000,
  "INTEREST_RATE": 1.5,
  "TOTAL_DUE_BEFORE_CLOSING": 9500,
  "MIN_PAYMENT": 500,
  "DUE_AT_CLOSING": 500,
  "FIRST_MONTH": 0
}
"""

  Scenario: The contract gets initialized with the total amount from the contract
    Then the initial state should be
"""
{
  "$class": "org.accordproject.installmentsale.InstallmentSaleState",
  "status" : "WaitingForFirstDayOfNextMonth",
  "balance_remaining" : 10000.00,
	"total_paid" : 0.00,
  "next_payment_month" : 0
}
"""

  Scenario: The contract accepts a first payment, and maintain the remaining balance
    Given the state
"""
{
  "$class": "org.accordproject.installmentsale.InstallmentSaleState",
  "status" : "WaitingForFirstDayOfNextMonth",
  "balance_remaining" : 10000.00,
	"total_paid" : 0.00,
  "next_payment_month" : 0
}
"""
    When it receives the request
"""
{
    "$class": "org.accordproject.installmentsale.Installment",
    "amount": 2500.00
}
"""
    Then it should respond with
"""
{
  "total_paid": 2500,
  "balance": 7612.499999999999,
  "$class": "org.accordproject.installmentsale.Balance"
}
"""
    And the following obligations have been emitted
"""
[
  {
    "$class": "org.accordproject.installmentsale.PaymentObligation",
    "amount": 2500,
    "from": "Dan",
    "to": "Ned",
    "eventId": "valid"
  }
]
"""
    And the new state of the contract should be
"""
{
  "$class": "org.accordproject.installmentsale.InstallmentSaleState",
  "status" : "WaitingForFirstDayOfNextMonth",
  "balance_remaining" : 7612.499999999999,
	"total_paid" : 2500,
  "next_payment_month" : 1
}
"""

  Scenario: The contract accepts a second payment, and maintain the remaining balance
    When it is in the state
"""
{
  "$class": "org.accordproject.installmentsale.InstallmentSaleState",
  "status" : "WaitingForFirstDayOfNextMonth",
  "balance_remaining" : 7612.499999999999,
	"total_paid" : 2500,
  "next_payment_month" : 1
}
"""
    And it receives the request
"""
{
    "$class": "org.accordproject.installmentsale.Installment",
    "amount": 2500.00
}
"""
    Then the new state of the contract should be
"""
{
  "$class": "org.accordproject.installmentsale.InstallmentSaleState",
  "status" : "WaitingForFirstDayOfNextMonth",
  "balance_remaining" : 5189.187499999998,
	"total_paid" : 5000,
  "next_payment_month" : 2
}
"""
    And the following obligations have been emitted
"""
[
  {
    "$class": "org.accordproject.installmentsale.PaymentObligation",
    "amount": 2500,
    "from": "Dan",
    "to": "Ned",
    "eventId": "valid"
  }
]
"""
    And it should respond with
"""
{
  "total_paid": 5000,
  "balance": 5189.187499999998,
  "$class": "org.accordproject.installmentsale.Balance"
}
"""

  Scenario: The contract accepts a third payment, and maintain the remaining balance
    When it is in the state
"""
{
  "$class": "org.accordproject.installmentsale.InstallmentSaleState",
  "status" : "WaitingForFirstDayOfNextMonth",
  "balance_remaining" : 5189.187499999998,
	"total_paid" : 2500,
  "next_payment_month" : 2
}
"""
    And it receives the request
"""
{
    "$class": "org.accordproject.installmentsale.Installment",
    "amount": 2500.00
}
"""
    Then the following obligations have been emitted
"""
[
  {
    "$class": "org.accordproject.installmentsale.PaymentObligation",
    "amount": 2500,
    "from": "Dan",
    "to": "Ned",
    "eventId": "valid"
  }
]
"""
    And the new state of the contract should be
"""
{
  "$class": "org.accordproject.installmentsale.InstallmentSaleState",
  "status" : "WaitingForFirstDayOfNextMonth",
  "balance_remaining" : 2729.525312499998,
	"total_paid" : 5000,
  "next_payment_month" : 3
}
"""
    And it should respond with
"""
{
  "total_paid": 5000,
  "balance": 2729.525312499998,
  "$class": "org.accordproject.installmentsale.Balance"
}
"""

