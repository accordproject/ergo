Feature: Late delivery contract
  This describe the expected behavior for the Accord Project's late delivery and penalty contract

  Background:
    Given the Ergo contract "org.accordproject.latedeliveryandpenalty.LateDeliveryAndPenalty" in file "examples/latedeliveryandpenalty/logic.ergo"
    And the model in file "examples/latedeliveryandpenalty/model.cto"
    And the contract data
"""
{
  "$class": "org.accordproject.latedeliveryandpenalty.TemplateModel",
  "forceMajeure": true,
  "penaltyDuration": {
    "$class": "org.accordproject.time.Duration",
    "amount": 2,
    "unit": "days"
  },
  "penaltyPercentage": 10.5,
  "capPercentage": 55,
  "termination": {
    "$class": "org.accordproject.time.Duration",
    "amount": 15,
    "unit": "days"
  },
  "fractionalPart": "days"
}
"""

  Scenario: The contract gets initialized
    Then the initial state should be the default state

  Scenario: The contract should return an error if called before the expected delivery date
    When the current time is "2019-01-11T16:34:00-05:00"
    And it receives the request
"""
{
    "$class": "org.accordproject.latedeliveryandpenalty.LateDeliveryAndPenaltyRequest",
    "forceMajeure": false,
    "agreedDelivery": "2019-01-31 03:24:00Z",
    "deliveredAt": null,
    "goodsValue": 200.00
}
"""
    Then it should fail with the error
"""
[Ergo] Cannot exercise late delivery before delivery date
"""

  Scenario: The contract should return the penalty amount but not allow the buyer to terminate
    When the current time is "2019-01-11T16:34:00-05:00"
    When it receives the request
"""
{
    "$class": "org.accordproject.latedeliveryandpenalty.LateDeliveryAndPenaltyRequest",
    "forceMajeure": false,
    "agreedDelivery": "2018-12-31 03:24:00Z",
    "deliveredAt": null,
    "goodsValue": 200.00
}
"""
    Then it should respond with
"""
{
  "$class": "org.accordproject.latedeliveryandpenalty.LateDeliveryAndPenaltyResponse",
  "buyerMayTerminate": false,
  "penalty": 110
}
"""

  Scenario: The contract should return the penalty amount and allow the buyer to terminate
    When the current time is "2019-01-11T16:34:00-05:00"
    When it receives the request
"""
{
    "$class": "org.accordproject.latedeliveryandpenalty.LateDeliveryAndPenaltyRequest",
    "forceMajeure": false,
    "agreedDelivery": "2018-01-31 03:24:00Z",
    "deliveredAt": null,
    "goodsValue": 200.00
}
"""
    Then it should respond with
"""
{
  "$class": "org.accordproject.latedeliveryandpenalty.LateDeliveryAndPenaltyResponse",
  "buyerMayTerminate": true,
  "penalty": 110
}
"""

