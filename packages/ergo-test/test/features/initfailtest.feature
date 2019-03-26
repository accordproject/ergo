Feature: Init test fail
  This describe the expected behavior for Ergo compiler when the init call is executed, but returns an error.

  Background:
    Given the Ergo contract "org.accordproject.initfailtest.InitFailTest" in file "examples/initfailtest/logic.ergo"
    And the model in file "examples/initfailtest/model.cto"
    And the contract data
"""
{
  "$class": "org.accordproject.initfailtest.TemplateModel"
}
"""

  Scenario: The contract should fail initializing
    Then it should fail to initialize with the error
"""
[Ergo] Enforce Error at 18:2-21:3 ''
"""

