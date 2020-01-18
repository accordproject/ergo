Feature: Init emit test
  This describe the expected behavior for Ergo compiler when the init call includes some emitted events.

  Background:
    Given the Ergo contract "org.accordproject.initemittest.InitEmitTest" in file "../../../tests/initemittest/logic/logic.ergo"
    And the model in file "../../../tests/initemittest/model/model.cto"
    And the contract data
"""
{
  "$class": "org.accordproject.initemittest.TemplateModel"
}
"""

  Scenario: The contract should emit a greeting during initialization
    Then the initial state should be
"""
{
  "$class": "org.accordproject.initemittest.State"
}
"""
    And the following initial obligations have been emitted
"""
[
  {
    "$class": "org.accordproject.initemittest.Greeting",
    "message": "Voila!"
  }
]
"""
