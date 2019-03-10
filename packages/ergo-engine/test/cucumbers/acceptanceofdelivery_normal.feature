Feature: Acceptance of delivery Contract
  This describes the expected behavior for the Accord Project's Acceptance of delivery contract

  Background:
    Given the Ergo contract "org.accordproject.acceptanceofdelivery.AcceptanceOfDelivery" in file "data/acceptance-of-delivery/logic.ergo"
    And the model in file "data/acceptance-of-delivery/model.cto"
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

  Scenario: The contract should accept inspection if received within delivery period
    When it receives the request
"""
{
    "$class":"org.accordproject.acceptanceofdelivery.InspectDeliverable",
    "deliverableReceivedAt": "08 Mar 2019 16:34:00 EST",
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

