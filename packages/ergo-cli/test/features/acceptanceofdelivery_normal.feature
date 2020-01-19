Feature: Acceptance of delivery Contract
  This describes the expected behavior for the Accord Project's Acceptance of delivery contract

  Background:
    Given the Ergo contract "org.accordproject.acceptanceofdelivery.AcceptanceOfDelivery" in file "../../../tests/acceptance-of-delivery/logic/logic.ergo"
    And the model in file "../../../tests/acceptance-of-delivery/model/model.cto"
    And the contract data
"""
{
  "$class": "org.accordproject.acceptanceofdelivery.TemplateModel",
  "shipper": "Party A",
  "receiver": "Party B",
  "deliverable": "Widgets",
  "businessDays": 10,
  "attachment": "Attachment X"
}
"""

  Scenario: The contract gets initialized
    Then the initial state should be the default state

  Scenario: The contract gets initialized, with a current time
    When the current time is "2019-01-11T16:34:00-05:00"
    Then the initial state should be the default state

  Scenario: The contract should accept inspection if received within delivery period
    When the current time is "2019-01-11T16:34:00-05:00"
    And it receives the request
"""
{
    "$class":"org.accordproject.acceptanceofdelivery.InspectDeliverable",
    "deliverableReceivedAt": "2019-01-08T16:34:00-05:00",
    "inspectionPassed": true
}
"""
    Then it should respond with
"""
{
  "receiver": "Party B",
  "shipper": "Party A",
  "status": "PASSED_TESTING",
  "$class": "org.accordproject.acceptanceofdelivery.InspectionResponse"
}
"""

