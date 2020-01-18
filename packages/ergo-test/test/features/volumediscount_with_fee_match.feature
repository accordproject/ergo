Feature: Volume discount (with fee)
  This describe the expected behavior for an alternative version of the Accord Project's volume discount contract with a fixed fee added using a match expression

  Background:
    Given the model in file "../../../tests/volumediscount4/model/model.cto"
    And the Ergo contract "org.accordproject.volumediscount.VolumeDiscount" in file "../../../tests/volumediscount4/logic/logic4.ergo"
    And the contract data
"""
{
  "$class": "org.accordproject.volumediscount.VolumeDiscountContract",
  "parties": null,
  "contractId": "cr1",
  "firstVolume": 1,
  "secondVolume": 10,
  "firstRate": 3,
  "secondRate": 2.9,
  "thirdRate": 2.8
}
"""

  Scenario: The contract gets initialized
    Then the initial state should be the default state

  Scenario: The vendor has a sales volume in the low range
    When it receives the request
"""
{
    "$class": "org.accordproject.volumediscount.VolumeDiscountRequest",
    "netAnnualChargeVolume": 0.6
}
"""
    Then it should respond with
"""
{
  "$class": "org.accordproject.volumediscount.VolumeDiscountResponse",
  "discountRate": 3.1
}
"""

  Scenario: The vendor has a sales volume in the medium range
    When it receives the request
"""
{
    "$class": "org.accordproject.volumediscount.VolumeDiscountRequest",
    "netAnnualChargeVolume": 3.4
}
"""
    Then it should respond with
"""
{
  "$class": "org.accordproject.volumediscount.VolumeDiscountResponse",
  "discountRate": 3.0
}
"""

  Scenario: The vendor has a sales volume in the high range
    When it receives the request
"""
{
    "$class": "org.accordproject.volumediscount.VolumeDiscountRequest",
    "netAnnualChargeVolume": 10.4
}
"""
    Then it should respond with
"""
{
  "$class": "org.accordproject.volumediscount.VolumeDiscountResponse",
  "discountRate": 2.9
}
"""

