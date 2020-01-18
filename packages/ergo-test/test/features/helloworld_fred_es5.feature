Feature: Fred Blog's Hello World
  This describe the expected behavior for the Accord Project's helloworld contract for Fred Blog

  Background:
    Given the Ergo contract "org.accordproject.helloworld.HelloWorld" in file "../../../tests/helloworld/logic/logic.ergo"
    And the model in file "../../../tests/helloworld/model/model.cto"
    And the contract data
"""
{
  "$class": "org.accordproject.helloworld.TemplateModel",
  "name": "Fred Blogs"
}
"""
    And the target platform "es6"

  Scenario: The contract gets initialized
    Then the initial state should be the default state

  Scenario: The contract says hello to Fred Blogs from Accord Project
    When it receives the request
"""
{
    "$class": "org.accordproject.helloworld.Request",
    "input": "Accord Project"
}
"""
    Then it should respond with
"""
{
  "$class": "org.accordproject.helloworld.Response",
  "output" : "Hello Fred Blogs (Accord Project)"
}
"""

  Scenario: The contract says hello to Fred Blogs from ACME
    When it receives the request
"""
{
    "$class": "org.accordproject.helloworld.Request",
    "input": "ACME"
}
"""
    Then it should respond with
"""
{
  "$class": "org.accordproject.helloworld.Response",
  "output" : "Hello Fred Blogs (ACME)"
}
"""

