Feature: Bad logic
  This describe the expected behavior for Ergo compiler when a function has duplicate bindings.

  Background:
    Given the Ergo contract "org.accordproject.helloworld.HelloWorld" in file "../../../tests/bad-function/logic/logic.ergo"
    And the model in file "../../../tests/helloworld/model/model.cto"
    And the contract data
"""
{
  "$class": "org.accordproject.helloworld.TemplateModel",
  "name": "Fred Blogs"
}
"""

  Scenario: The contract should fail executing when a function declares the same parameter twice
    When it receives the request
"""
{
    "$class": "org.accordproject.helloworld.Request",
    "input": "Accord Project"
}
"""
    Then it should fail with the error
"""
Compilation error (at file ../../../tests/bad-function/logic/logic.ergo line 17 col 0). Variable 'a' is bound multiple times in 'org.accordproject.helloworld.f'
define function f(a:Integer, a:String) {
^                                       
"""

