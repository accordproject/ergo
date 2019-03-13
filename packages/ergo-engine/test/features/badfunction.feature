Feature: Bad logic
  This describe the expected behavior for Ergo compiler when a function has duplicate bindings.

  Background:
    Given the Ergo contract "org.accordproject.helloworld.HelloWorld" in file "examples/bad-function/logic.ergo"
    And the model in file "examples/helloworld/model.cto"
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
{
    "kind": "CompilationError",
    "message": "Variable 'a' is bound multiple times in 'org.accordproject.helloworld.f'",
    "locstart": {
      "line": 17,
      "character": 0
    },
    "locend": {
      "line": 19,
      "character": 1
    }
}
"""

