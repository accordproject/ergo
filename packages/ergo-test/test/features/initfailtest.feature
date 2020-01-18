Feature: Init test fail
  This describe the expected behavior for Ergo compiler when the init call is executed, but returns an error.

  Background:
    Given the Ergo contract "org.accordproject.initfailtest.InitFailTest" in file "../../../tests/initfailtest/logic/logic.ergo"
    And the model in file "../../../tests/initfailtest/model/model.cto"
    And the contract data
"""
{
  "$class": "org.accordproject.initfailtest.TemplateModel"
}
"""

  Scenario: The contract should fail initializing
    Then it should fail to initialize with the error
"""
[Ergo] Enforce Error at 19:2-22:3 ''
"""

