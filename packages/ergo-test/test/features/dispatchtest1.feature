Feature: Dispatch Tests
  This describe the expected behavior when dispatching requests to a clause

  Background:
    Given the Ergo contract "org.accordproject.dispatchtest.DispatchTest" in file "../../../tests/dispatchtest/logic/logic.ergo"
    And the model in file "../../../tests/dispatchtest/model/model.cto"
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
Compilation error (at file ../../../tests/dispatchtest/logic/logic.ergo line 17 col 0). Multiple clauses can process the request 'org.accordproject.dispatchtest.Request4'
contract DispatchTest over TemplateModel {
^                                         
"""

