Feature: Bad logic
  This describe the expected behavior for Ergo compiler when a clause has duplicate bindings.

  Background:
    Given the Ergo contract "org.accordproject.helloworld.HelloWorld" in file "data/bad-function/logic2.ergo"
    And the model in file "data/helloworld/model.cto"
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
{
    "kind": "CompilationError",
    "message": "Variable 'request' is bound multiple times in 'helloworld'",
    "locstart": {
      "line": 19,
      "character": 2
    },
    "locend": {
      "line": 21,
      "character": 3
    }
}
"""

