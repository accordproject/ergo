Feature: starOf and endOf with time periods test
  This describe the expected behavior for Ergo compiler when using integer literals

  Background:
    Given the Ergo contract "org.accordproject.startendtest.StartEndTest" in file "examples/startendtest/logic.ergo"
    And the model in file "examples/startendtest/model.cto"
    And the contract data
"""
{
  "$class": "org.accordproject.startendtest.TemplateModel"
}
"""

  Scenario: The contract should initialize
    Then the initial state should be the default state

  Scenario: The contract should return the correct response
    When the current time is "2019-01-01T12:00:00+04:00"
    And it receives the request
"""
{
    "$class": "org.accordproject.startendtest.Request",
    "date": "2018-01-01T12:00:00+04:00"
}
"""
    Then it should respond with
"""
{
    "$class": "org.accordproject.startendtest.TestResponse",
    "now": "2019-01-01T12:00:00.000+04:00",
    "date": "2018-01-01T12:00:00.000+04:00",
    "dateFormat": "2018/03/31",
    "startOfDay": "2018-01-01T00:00:00.000+04:00",
    "endOfDay": "2018-01-01T23:59:59.999+04:00"
}
"""

  Scenario: The contract should return the correct response
    When the current time is "2019-01-01T12:00:00-11:00"
    And it receives the request
"""
{
    "$class": "org.accordproject.startendtest.Request",
    "date": "2018-01-01T12:00:00-11:00"
}
"""
    Then it should respond with
"""
{
    "$class": "org.accordproject.startendtest.TestResponse",
    "now": "2019-01-01T12:00:00.000-11:00",
    "date": "2018-01-01T12:00:00.000-11:00",
    "dateFormat": "2018/03/31",
    "startOfDay": "2018-01-01T00:00:00.000-11:00",
    "endOfDay": "2018-01-01T23:59:59.999-11:00"
}
"""

  Scenario: The contract should return the correct response
    When the current time is "2019-01-01T12:00:00-05:00"
    And it receives the request
"""
{
    "$class": "org.accordproject.startendtest.Request",
    "date": "2018-01-01T23:00:00-11:00"
}
"""
    Then it should respond with
"""
{
    "$class": "org.accordproject.startendtest.TestResponse",
    "now": "2019-01-01T12:00:00.000-05:00",
    "date": "2018-01-01T23:00:00.000-11:00",
    "dateFormat": "2018/03/31",
    "startOfDay": "2018-01-02T00:00:00.000-05:00",
    "endOfDay": "2018-01-02T23:59:59.999-05:00"
}
"""

