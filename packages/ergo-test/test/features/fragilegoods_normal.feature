Feature: Fragile goods Contract
  This describes the expected behavior for the Accord Project's Fragile goods contract

  Background:
    Given the Ergo contract "io.clause.demo.fragileGoods.FragileGoods" in file "../../../tests/fragilegoods/logic/logic.ergo"
    And the model in file "../../../tests/fragilegoods/model/model.cto"
    And the contract data
"""
{
  "$class": "io.clause.demo.fragileGoods.TemplateModel",
  "deliveryPrice": 1000,
  "accelerationMin": -0.5,
  "accelerationMax": 0.5,
  "accelerationBreachPenalty": 5,
  "deliveryLimitDuration": {
    "$class": "io.clause.demo.fragileGoods.Duration",
    "amount": 10,
    "unit": "seconds"
  },
  "lateDeliveryPenalty": 200
}
"""

  Scenario: The contract gets initialized
    Then the initial state should be the default state

  Scenario: The contract should return the final amount for the delivery with penalty
    When it receives the request
"""
{
    "$class": "io.clause.demo.fragileGoods.DeliveryUpdate",
    "startTime":"2018-01-01T16:34:00Z",
    "finishTime":"2018-01-01T16:34:11Z",
    "status":"ARRIVED",
    "accelerometerReadings":[0.2,0.6,-0.3,-0.7,0.1]
}
"""
    Then it should respond with
"""
{
  "amount": 990,
  "$class": "io.clause.demo.fragileGoods.PayOut"
}
"""

  Scenario: The contract should return the final amount for the delivery with no shock penalty
    When it receives the request
"""
{
    "$class": "io.clause.demo.fragileGoods.DeliveryUpdate",
    "startTime":"2018-01-01T16:34:00Z",
    "finishTime":"2018-01-01T16:34:11Z",
    "status":"ARRIVED",
    "accelerometerReadings":[0.2,-0.3,0.1]
}
"""
    Then it should respond with
"""
{
  "amount": 1000,
  "$class": "io.clause.demo.fragileGoods.PayOut"
}
"""

