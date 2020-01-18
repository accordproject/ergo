Feature: Bad logic
  This describe the expected behavior for Ergo compiler when a clause has duplicate bindings.

  Background:
    Given the Ergo contract "org.accordproject.helloworld.HelloWorld" in file "../../../tests/bad-function2/logic/logic2.ergo"
    And the model in file "../../../tests/bad-function2/model/model.cto"
    And the contract data
"""
{
  "$class": "org.accordproject.helloworld.TemplateModel",
  "name": "Fred Blogs"
}
"""

  Scenario: The contract should fail executing when a clause declares the same parameter twice
    When it receives the request
"""
{
    "$class": "org.accordproject.helloworld.Request",
    "input": "Accord Project"
}
"""
    Then it should fail with the error
"""
Compilation error (at file ../../../tests/bad-function2/logic/logic2.ergo line 19 col 2). Variable 'request' is bound multiple times in 'helloworld'
  clause helloworld(request : Request, request: Integer) : Response {
  ^                                                                  
"""

