Feature: Integer test
  This describe the expected behavior for Ergo compiler when using integer literals

  Background:
    Given the Ergo contract "org.accordproject.integertest.IntegerTest" in file "../../../tests/integertest/logic/logic.ergo"
    And the model in file "../../../tests/integertest/model/model.cto"
    And the contract data
"""
{
  "$class": "org.accordproject.integertest.TemplateModel"
}
"""

  Scenario: The contract should initialize
    Then the initial state should be the default state

  Scenario: The contract should return the correct response
    When it receives the request
"""
{
    "$class": "org.accordproject.integertest.Request"
}
"""
    Then it should respond with
"""
{
  "$class": "org.accordproject.integertest.Response",
 	"test1": 0,
	"test2": 0,
  "test3": 0
}
"""

