Feature: Inheritance test
  This describe the expected behavior for Ergo compiler when handling requests which exploit inheritance.

  Background:
    Given the Ergo contract "org.accordproject.inheritancetest.InheritanceTest" in file "../../../tests/inheritancetest/logic/logic.ergo"
    And the model in file "../../../tests/inheritancetest/model/model.cto"
    And the contract data
"""
{
  "$class": "org.accordproject.inheritancetest.TemplateModel"
}
"""

  Scenario: The contract should initialize
    Then the initial state should be the default state

  Scenario: The contract should return the correct response on a request
    When it receives the request
"""
{
    "$class": "org.accordproject.inheritancetest.Request"
}
"""
    Then it should respond with
"""
{
  "$class": "org.accordproject.inheritancetest.SubSubResponse",
 	"test1": 0,
	"test2": 0.5
}
"""

  Scenario: The contract should return the correct response on a sub-request
    When it receives the request
"""
{
  "$class": "org.accordproject.inheritancetest.SubRequest",
 	"test1": 0
}
"""
    Then it should respond with
"""
{
  "$class": "org.accordproject.inheritancetest.SubSubResponse",
 	"test1": 0,
	"test2": 0.5
}
"""

  Scenario: The contract should return the correct response on a sub-sub-request
    When it receives the request
"""
{
  "$class": "org.accordproject.inheritancetest.SubSubRequest",
 	"test1": 0,
	"test2": 0.5
}
"""
    Then it should respond with
"""
{
  "$class": "org.accordproject.inheritancetest.SubSubResponse",
 	"test1": 0,
	"test2": 0.5
}
"""

