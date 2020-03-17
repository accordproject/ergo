This is a fixed interest loan to the amount of {{loanAmount}}
at the yearly interest rate of {{rate}}%
with a loan term of {{loanDuration}},
and monthly payments of {{% monetaryAmountFormat(monthlyPaymentFormula(contract.loanAmount,contract.rate,contract.loanDuration), "0,0.0 CCC") %}}
