## What is Ergo?

Ergo is a domain specific language (DSL) to capture the logic of *legal* contracts. It is part of the Accord Project and integrates with the open source [Cicero](https://github.com/accordproject/cicero) implementation for the [Accord Project template specification](https://docs.google.com/document/d/1TxqtWgT4OcGozWAJpIC-bwrj4AOWoPXmEAoOcfMuRCM).

_Both the design and implementation of Ergo are in early stages. We encourage you to visit this site regularly for updates and future releases information._

## Overview

Ergo's high-level goals and requirements are:
- to have contracts and clauses as first-class elements of the language
- to help legal-tech developers quickly and safely write computable legal contracts
- to be modular, facilitating reuse of existing contract or clause logic
- to ensure safe execution: the language should prevent run-time errors and non-terminating logic
- to be blockchain neutral: the same contract logic can be executed either on and off chain on a variety of distributed ledger technologies
- to be formally specified: the meaning of contracts should be well defined so it can be verified, and preserved during execution
- to be consistent with the [Accord Project Template Specification](https://docs.google.com/document/d/1UacA_r2KGcBA2D4voDgGE8jqid-Uh4Dt09AE-shBKR0)

## Status and Contributions

Ergo is developed as an open standard as part of the <a href="https://www.accordproject.org">Accord Project</a>. An open-source implementation is tracking the standard closely, and is available as an npm package or on [github](https://github.com/accordproject/ergo). Installation instructions can be found [here](http://ergo.readthedocs.io/en/latest/Installation.html).

Information about how to contribute to Ergo can be found in [contributing.md](https://github.com/accordproject/ergo/blob/master/contribute-to-ergo/contributing.md).

## An example

To give you a taste of Ergo, here is a simple simple installment sale. Legal templates in the Accord Project have three components: a natural language grammar, a model, and some logic.

The natural language template describes the terms of the contract, and uses markup to indicate the contract variables such as the parties (`[{BUYER}]` and `[{SELLER}]`), the financial terms (e.g., `[{INTEREST_RATE}]`), or obligations (e.g., `[{MIN_PAYMENT}]` for each installment).

```
[{BUYER}] agrees to pay to [{SELLER}] the total sum e[{INITIAL_DUE}], in the manner following:

E[{DUE_AT_CLOSING}] is to be paid at closing, and the remaining balance of E[{TOTAL_DUE_BEFORE_CLOSING}] shall be paid as follows:

E[{MIN_PAYMENT}] or more per month on the first day of each and every month, and continuing until the entire balance, including both principal and interest, shall be paid in full -- provided, however, that the entire balance due plus accrued interest and any other amounts due here-under shall be paid in full on or before 24 months.

Monthly payments shall include both principal and interest with interest at the rate of [{INTEREST_RATE}]%, computed monthly on the remaining balance from time to time unpaid.
```

The model describes the structure and types for the contract variables, 

```go
namespace org.accordproject.installmentsale

contract InstallmentSale over TemplateModel {
  // This clause applies for installments
  clause PayInstallment(request : Installment) : Balance {
    // Enforce clause preconditions
    enforce (state.status = "WaitingForFirstDayOfNextMonth"); // This clause only applies when waiting for next installment
    enforce (contract.MIN_PAYMENT <= request.amount);    // Underpaying is forbidden
    enforce (request.amount <= state.balance_remaining); // overpaying is forbidden.

    // Computes the new balance and the total amount paid
    define variable before_interest = state.balance_remaining - request.amount;
    define variable balance = before_interest * (1.0 + contract.INTEREST_RATE/100.00);
		define variable total_paid = state.total_paid + request.amount;

    // Sets the remaining balance and the 
    set state new InstallmentSaleState{
      status: "WaitingForFirstDayOfNextMonth",
      balance_remaining: balance,
			total_paid: total_paid
    };
		emit new PaymentObligation{
			from: contract.BUYER,
			to: contract.SELLER,
			amount: request.amount
		};
    return new Balance{
      balance: balance
    }
  }

  // This clause applies at closing
  clause PayLastInstallment(request : ClosingPayment) : Balance {
    // 
    enforce (request.amount = state.balance_remaining + contract.DUE_AT_CLOSING);
    define variable total_paid = state.total_paid + request.amount;
    set state new InstallmentSaleState{
      status: "Fulfilled",
      balance_remaining: 0.0,
			total_paid: total_paid
    };
		emit new PaymentObligation{
			from: contract.BUYER,
			to: contract.SELLER,
			amount: request.amount
		};
    return new Balance{
      balance: balance,
			total_paid: total_paid
    }
  }
}
