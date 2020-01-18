Feature: Shadowing test
  This describe the expected behavior for Ergo compiler when calling consecutive functions with the same variable names

  Background:
    Given the Ergo contract "org.accordproject.shadowingtest.ShadowingTest" in file "../../../tests/shadowingtest/logic/logic.ergo"
    And the model in file "../../../tests/shadowingtest/model/model.cto"
    And the contract data
"""
{
  "$class": "org.accordproject.shadowingtest.TemplateModel"
}
"""

  Scenario: The contract should initialize
    Then the initial state should be the default state

  Scenario: The contract should return the correct response
    When it receives the request
"""
{
    "$class": "org.accordproject.shadowingtest.Request1"
}
"""
    Then it should respond with
"""
{
  "$class": "org.accordproject.shadowingtest.Response",
 	"x": 0.0,
	"y": 22.0
}
"""

