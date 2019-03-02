Feature: Dispatch Tests
  This describe the expected behavior when dispatching requests to a clause

  Background:
    Given the Ergo contract "org.accordproject.dispatchtest.DispatchTest" in file "data/dispatchtest/logic.ergo"
    And the model in file "data/dispatchtest/model.cto"
    And the contract data
"""
{
  "$class": "org.accordproject.dispatchtest.TemplateModel"
}
"""

  Scenario: The contract should fail executing when an import is missing
    When it receives the request
"""
{
    "$class": "org.accordproject.dispatchtest.Request1"
}
"""
    Then it should fail with the error
"""
{
    "kind": "CompilationError",
    "message": "Multiple clauses can process the request 'org.accordproject.dispatchtest.Request4'",
    "locstart": {
      "line": 16,
      "character": 0
    },
    "locend": {
      "line": 37,
      "character": 1
    }
}
"""

