Feature: Dispatch Tests
  This describe the expected behavior when dispatching requests to a clause

  Background:
    Given the Ergo contract "org.accordproject.dispatchtest.DispatchTest" in file "../../../tests/dispatchtest3/logic/logic3.ergo"
    And the model in file "../../../tests/dispatchtest3/model/model.cto"
    And the contract data
"""
{
  "$class": "org.accordproject.dispatchtest.TemplateModel"
}
"""

  Scenario: The contract should initialize
    Then the initial state should be the default state

  Scenario: The contract should return the correct response for a Request1
    When it receives the request
"""
{
    "$class": "org.accordproject.dispatchtest.Request1"
}
"""
    Then it should respond with
"""
{
    "message": "I am a request1",
    "$class": "org.accordproject.dispatchtest.Response"
}
"""

  Scenario: The contract should return the correct response for a Request2
    When it receives the request
"""
{
    "$class": "org.accordproject.dispatchtest.Request2"
}
"""
    Then it should respond with
"""
{
    "message": "I am a request1",
    "$class": "org.accordproject.dispatchtest.Response"
}
"""

  Scenario: The contract should return the correct response for a Request3
    When it receives the request
"""
{
    "$class": "org.accordproject.dispatchtest.Request3"
}
"""
    Then it should respond with
"""
{
    "message": "I am a request3",
    "$class": "org.accordproject.dispatchtest.Response"
}
"""

  Scenario: The contract should return the correct response for a Request4
    When it receives the request
"""
{
    "$class": "org.accordproject.dispatchtest.Request4"
}
"""
    Then it should respond with
"""
{
    "message": "I am a request4",
    "$class": "org.accordproject.dispatchtest.Response"
}
"""

  Scenario: The contract should return the correct response for a Request5
    When it receives the request
"""
{
    "$class": "org.accordproject.dispatchtest.Request5"
}
"""
    Then it should fail with the error
"""
[Ergo] Dispatch Error: no clause in the contract matches the request
"""

  Scenario: The contract should return the correct response for a Request6
    When it receives the request
"""
{
    "$class": "org.accordproject.dispatchtest.Request6"
}
"""
    Then it should respond with
"""
{
    "message": "I am a request6",
    "$class": "org.accordproject.dispatchtest.Response"
}
"""

