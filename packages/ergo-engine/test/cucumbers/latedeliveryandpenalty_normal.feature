Feature: Late delivery contract
  This describe the expected behavior for the Accord Project's late delivery and penalty contract

  Background:
    Given the Ergo contract "org.accordproject.latedeliveryandpenalty.LateDeliveryAndPenalty" in file "data/latedeliveryandpenalty/logic.ergo"
    And the model in file "data/latedeliveryandpenalty/model.cto"
    And the model in file "data/latedeliveryandpenalty/test.cto"
    And the contract data
"""
{
  "$class": "org.accordproject.latedeliveryandpenalty.TemplateModel",
  "forceMajeure": true,
  "penaltyDuration": {
    "$class": "org.accordproject.base.Duration",
    "amount": 2,
    "unit": "DAY"
  },
  "penaltyPercentage": 10.5,
  "capPercentage": 55,
  "termination": {
    "$class": "org.accordproject.base.Duration",
    "amount": 15,
    "unit": "DAY"
  },
  "fractionalPart": "DAY"
}
"""

  Scenario: The contract gets initialized
    Then the initial state should be the default state

  Scenario: The contract should return the penalty amount but not allow the buyer to terminate
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

  Scenario: The contract should return an error if called before the expected delivery date
    When it receives the request
"""
{
    "$class": "org.accordproject.latedeliveryandpenalty.LateDeliveryAndPenaltyRequest",
    "forceMajeure": false,
    "agreedDelivery": "2019-03-31 03:24:00Z",
    "deliveredAt": null,
    "goodsValue": 200.00
}
"""
    Then it should fail with the error
"""
{
  "kind": "ErgoError",
  "message": {
      "$class": "org.accordproject.ergo.stdlib.ErgoErrorResponse",
      "message": "Cannot exercise late delivery before delivery date"
  }
}
"""

