Feature: Late delivery contract
  This describe the expected behavior for the Accord Project's late delivery and penalty contract

  Background:
    Given the Ergo contract "org.accordproject.latedeliveryandpenalty.LateDeliveryAndPenalty" in file "../../../tests/latedeliveryandpenalty2/logic/logic.ergo"
    And the model in file "../../../tests/latedeliveryandpenalty2/model/model2.cto"
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

  Scenario: The contract should fail initializing when an import is missing
    Then it should fail to initialize with the error
"""
Namespace is not defined for type org.accordproject.test.* File '../../../tests/latedeliveryandpenalty2/model/model2.cto': 
"""

  Scenario: The contract should fail executing when an import is missing
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
    Then it should fail with the error
"""
Namespace is not defined for type org.accordproject.test.* File '../../../tests/latedeliveryandpenalty2/model/model2.cto': 
"""

