/*
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

cheatsheet1 = (`\
import org.accordproject.cicero.contract.*
import org.accordproject.cicero.runtime.*

///
define concept ShippingContract {penalty : Double}
define concept LateRequest {weeks : Double}
define concept LateResponse {message: String}

///
define concept ShippingState {}
define concept InTransitState extends ShippingState {}
define concept DeliveredState extends ShippingState {}

///
define concept Cheating extends ErgoErrorResponse {}
define concept BillingEvent extends Event {amount: Double}

///
contract Shipping
  over ShippingContract
  state ShippingState
{
///
  clause init() : Unit
  {
    set state InTransitState {};
    return
  }
  
///
  clause late_delivery(req : LateRequest)
    : LateResponse
  {
///
    emit BillingEvent {
      amount:
      req.weeks * contract.penalty
    };

///
    enforce req.weeks > 0.0
    else throw Cheating{
      message: "Not actually late!"
    };

///
    set state DeliveredState {};

///
    return LateResponse{message: "Delivery processed."}
  }
}

///
set contract Shipping
  over ShippingContract {penalty : 5.0}

///
call init()
///
call late_delivery(LateRequest {weeks: 2.0})
///
call late_delivery(LateRequest {weeks: -1.0})
`).split('///\n');

cheatsheet2 = (`\
namespace org.accordproject.installmentsale

import org.accordproject.cicero.contract.*
import org.accordproject.cicero.runtime.*
import org.accordproject.money.MonetaryAmount

///
define asset InstallmentSaleContract extends AccordContract {
  BUYER : String,
  SELLER : String,
  INITIAL_DUE : Double,
  INTEREST_RATE : Double,
  TOTAL_DUE_BEFORE_CLOSING : Double,
  MIN_PAYMENT : Double,
  DUE_AT_CLOSING : Double
}

///
define asset InstallmentSaleState extends AccordContractState {
  status : String,
  balance_remaining : Double,
  next_payment_month : Integer,
  total_paid : Double
}

///
define concept Installment extends Request {
   amount : Double
}

define concept ClosingPayment extends Request {
}

///
define concept Balance extends Response {
  balance : Double,
  total_paid : Double
}

define event MyObligation {
  party : String
}
define event PaymentObligation extends MyObligation {
   amount : Double
}

///
contract InstallmentSale
  over InstallmentSaleContract
  state InstallmentSaleState
{
///
  clause init(request:Request) : Unit {
    set state InstallmentSaleState{
      stateId: "org.accordproject.installmentsale.InstallmentSaleState#1",
      status: "WaitingForFirstDayOfNextMonth",
      balance_remaining: contract.TOTAL_DUE_BEFORE_CLOSING,
      total_paid: 0.0,
      next_payment_month: 1
    };
    return
  }
///
  clause payInstallment(request : Installment) : Balance {
    let before_interest = state.balance_remaining - request.amount;
    let balance = before_interest * (1.0 + contract.INTEREST_RATE/100.00);
    let total_paid = state.total_paid + request.amount;

///
    set state InstallmentSaleState{
      stateId: "1",
      status: "WaitingForFirstDayOfNextMonth",
      balance_remaining: balance,
      total_paid: total_paid,
      next_payment_month: state.next_payment_month +i 1
    };
///
    emit PaymentObligation{
      party: contract.BUYER,
      amount: request.amount
    };
///
    return Balance{
      balance: balance,
      total_paid: total_paid
    }
  }
///
  clause payLastInstallment(request : ClosingPayment) : Balance {
    let finalAmount = contract.DUE_AT_CLOSING + state.balance_remaining;
    let total_paid = state.total_paid + finalAmount;
		let balance = 0.0;
    set state InstallmentSaleState{
      stateId: "1",
      status: "Fulfilled",
      balance_remaining: balance,
      total_paid: total_paid,
      next_payment_month: 0
    };
    emit PaymentObligation{
      party: contract.BUYER,
      amount: finalAmount
    };
    return Balance{
      balance: balance,
      total_paid: total_paid
    }
  }
}

///
set contract InstallmentSale over InstallmentSaleContract{
  contractId: "a0174e75-29d1-4323-a209-0531048abf9d",
  parties: none,
  BUYER : "Dan",
  SELLER : "Ned",
  INITIAL_DUE : 10000.0,
  INTEREST_RATE : 3.5,
  TOTAL_DUE_BEFORE_CLOSING : 9500.0,
  MIN_PAYMENT : 500.0,
  DUE_AT_CLOSING : 500.0
}
///
call init(Request{})
///
call payInstallment(Installment{ amount: 2000.00 })
///
call payInstallment(Installment{ amount: 2000.00 })
///
call payInstallment(Installment{ amount: 2000.00 })
///
call payInstallment(Installment{ amount: 2000.00 })
///
call payLastInstallment(ClosingPayment{})
`).split('///\n');

cheatsheet3 = (`\
namespace org.accordproject.safte

import org.accordproject.cicero.contract.*
import org.accordproject.cicero.runtime.*

///
// Contract parameters
define asset SafteContract extends AccordContract {
  companyName : String,
  purchaser : String,
  purchaseAmount : Double,
  discount : Double,
  projectName : String,
  amount : Double,
  months : Integer
}

///
// Contract state
define enum SafteStatus {
  PENDING, EXECUTED
}
define asset SafteState extends AccordContractState {
  status : SafteStatus
}

///
// Token sale Request/Response
define transaction TokenSale extends Request {
  tokenPrice : Double
}
define transaction TokenShare extends Response {
  tokenAmount : Double
}

// Equity financing Request/Response
define transaction EquityFinancing extends Request {
  sharePrice : Double
}
define transaction EquityShare extends Response {
  equityAmount : Double
}

// Dissolution Request/Response
define transaction DissolutionEvent extends Request {
  cause : String
}
define transaction PayOut extends Response {
 amount : Double
}

///
contract Safte
  over SafteContract
  state SafteState {
///
  clause init() : Unit {
    set state SafteState {
      stateId: "1",
      status: "PENDING"
    };
    return
  }

///
  clause tokenSale(request : TokenSale) : TokenShare {
    enforce state.status = "PENDING";
    let discountRate = (100.0 - contract.discount) / 100.00;
    let discountPrice = request.tokenPrice * discountRate;
    set state SafteState {
      stateId: "1",
      status: "EXECUTED"
    };
    return TokenShare{
      tokenAmount : contract.purchaseAmount / discountPrice
    }
  }

///
  clause equityFinancing(request : EquityFinancing) : EquityShare {
    enforce state.status = "PENDING";
    let discountRate = (100.0 - contract.discount) / 100.00;
    let discountPrice = request.sharePrice * discountRate;
    set state SafteState {
      stateId: "1",
      status: "EXECUTED"
    };
    return EquityShare{
      equityAmount : contract.purchaseAmount / discountPrice
    }
  }

///
  clause dissolutionEvent(request : DissolutionEvent) : PayOut {
    enforce state.status = "PENDING";
    set state SafteState {
      stateId: "1",
      status: "EXECUTED"
    };
    return PayOut{
      amount : contract.purchaseAmount
    }
  }
}

///
set contract Safte over SafteContract{
  contractId: "Umbrella#231",
  parties: none,
  companyName: "ACME",
  purchaser: "Dan",
  purchaseAmount: 25.0,
  discount: 7.0,
  projectName: "Umbrella Tokens",
  amount : 1000.0,
  months : 12
}

///
call init()
///
call dissolutionEvent(DissolutionEvent{ cause : "Cold feet" })
///
call tokenSale(TokenSale{ tokenPrice: 3.14 })
///
call init()
///
call tokenSale(TokenSale{ tokenPrice: 3.14 })
///
call init()
///
send TokenSale{ tokenPrice: 3.14 }
///
call init()
///
send DissolutionEvent{ cause : "Cold feet" }

`).split('///\n');

allcheatsheets = [cheatsheet1, cheatsheet2, cheatsheet3];
