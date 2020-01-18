Feature: Bad logic
  This describe the expected behavior for Ergo compiler when there is a parse error.

  Background:
    Given the Ergo contract "org.accordproject.helloworld.HelloWorld" in file "../../../tests/bad-logic/logic/logic.ergo"
    And the model in file "../../../tests/bad-logic/model/model.cto"
    And the contract data
"""
{
  "$class": "org.accordproject.helloworld.TemplateModel",
  "name": "Fred Blogs"
}
"""

  Scenario: The contract should fail executing when an import is missing
    When it receives the request
"""
{
    "$class": "org.accordproject.helloworld.Request",
    "input": "Accord Project"
}
"""
    Then it should fail with the error
"""
Parse error (at file ../../../tests/bad-logic/logic/logic.ergo line 17 col 20). 
contract HelloWorld ovr TemplateModel {
                    ^^^                
"""

