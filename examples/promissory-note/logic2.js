'use strict';
/*eslint-disable no-unused-vars*/
/*eslint-disable no-undef*/
/*eslint-disable no-var*/


function compoundInterestMultiple(context) {
  var vnumberOfDays = deref(context, "numberOfDays");
  var vannualInterest = deref(context, "annualInterest");
  return Math.pow((1.0 + vannualInterest), (vnumberOfDays / 365.0));
}
class PromissoryNote {
  main(context) {
    var vemit = deref(context, "emit");
    var vstate = deref(context, "state");
    var vcontract = deref(context, "contract");
    var vrequest = deref(context, "request");
    var vlcontract_0 = vcontract;
    var vlstate_0 = vstate;
    var vlemit_0 = vemit;
    var vX$match0_0 = vrequest;
    var res1 = null;
    if (either(cast(["org.accordproject.promissorynote.Request"],vX$match0_0))) {
      var vX$case0 = null;
      vX$case0 = toLeft(cast(["org.accordproject.promissorynote.Request"],vX$match0_0));
      res1 = {"left" : {"$main": vX$case0}};
    } else {
      var vX$case1 = null;
      vX$case1 = toRight(cast(["org.accordproject.promissorynote.Request"],vX$match0_0));
      res1 = {"right" : null};
    }
    var res8 = null;
    if (either(res1)) {
      var vX$case0_2 = null;
      vX$case0_2 = toLeft(res1);
      var vX$case0_1 = vX$case0_2;
      var vX$main = deref(vX$case0_1, "$main");
      var vrequest_0 = vX$main;
      var vlcontract = vcontract;
      var vlstate = vstate;
      var vlemit = vemit;
      var t7;
      if (!(!((compare(deref(unbrand(vlcontract), "annualInterest"),0.0) < 0)))) {
        t7 = {"right" : {"type": ["org.accordproject.ergo.Error"], "data": {"message": "Enforce condition failed"}}};
      } else {
        var t6;
        if (!(!((compare(deref(unbrand(vlcontract), "dollarAmount"),0.0) < 0)))) {
          t6 = {"right" : {"type": ["org.accordproject.ergo.Error"], "data": {"message": "Enforce condition failed"}}};
        } else {
          var voutstanding = (deref(unbrand(vlcontract), "dollarAmount") - deref(unbrand(vrequest_0), "amountPaid"));
          var t5;
          if (!(!((compare(voutstanding,0.0) < 0)))) {
            t5 = {"right" : {"type": ["org.accordproject.ergo.Error"], "data": {"message": "Enforce condition failed"}}};
          } else {
            var vp2 = deref(unbrand(vlcontract), "date");
            var vp1 = "17 May 2018 13:53:33 EST";
            var vp1 = dateTimeFromString(vp1);
            var vnumberOfDays_0 = dateTimeDurationBetween(vp1, vp2);
            var t4;
            if (!(!((compare(vnumberOfDays_0,0.0) < 0)))) {
              t4 = {"right" : {"type": ["org.accordproject.ergo.Error"], "data": {"message": "Enforce condition failed"}}};
            } else {
              var vnumberOfDays = vnumberOfDays_0;
              var vannualInterest = deref(unbrand(vlcontract), "interestRate");
              var vcompounded = (voutstanding * Math.pow((1.0 + vannualInterest), (vnumberOfDays / 365.0)));
              var vX$match0 = deref(unbrand(vlcontract), "interestRate");
              var res2 = null;
              if (either(vX$match0)) {
                var vX$case0 = null;
                vX$case0 = toLeft(vX$match0);
                res2 = {"left" : {"$option": vX$case0}};
              } else {
                var vX$case1 = null;
                vX$case1 = toRight(vX$match0);
                res2 = {"right" : null};
              }
              var res3 = null;
              if (either(res2)) {
                var vX$case0_0 = null;
                vX$case0_0 = toLeft(res2);
                var vX$case0 = vX$case0_0;
                var vX$option = deref(vX$case0, "$option");
                res3 = vX$option;
              } else {
                var vX$case1 = null;
                vX$case1 = toRight(res2);
                res3 = 3.4;
              }
              t4 = {"left" : concat({"emit": vlemit}, concat({"state": vlstate}, {"response": brand(["org.accordproject.promissorynote.Response"],concat({"rate": res3}, {"outstandingBalance": vcompounded}))}))};
            }
            t5 = t4;
          }
          t6 = t5;
        }
        t7 = t6;
      }
      res8 = t7;
    } else {
      var vX$case1 = null;
      vX$case1 = toRight(res1);
      res8 = {"right" : brand(["org.accordproject.promissorynote.Error"],{"message": ""})};
    }
    return res8;
  }
  check(context) {
    var vrequest = deref(context, "request");
    var vemit = deref(context, "emit");
    var vstate = deref(context, "state");
    var vcontract = deref(context, "contract");
    var vlcontract = vcontract;
    var vlstate = vstate;
    var vlemit = vemit;
    var t6;
    if (!(!((compare(deref(unbrand(vlcontract), "annualInterest"),0.0) < 0)))) {
      t6 = {"right" : {"type": ["org.accordproject.ergo.Error"], "data": {"message": "Enforce condition failed"}}};
    } else {
      var t5;
      if (!(!((compare(deref(unbrand(vlcontract), "dollarAmount"),0.0) < 0)))) {
        t5 = {"right" : {"type": ["org.accordproject.ergo.Error"], "data": {"message": "Enforce condition failed"}}};
      } else {
        var voutstanding = (deref(unbrand(vlcontract), "dollarAmount") - deref(unbrand(vrequest), "amountPaid"));
        var t4;
        if (!(!((compare(voutstanding,0.0) < 0)))) {
          t4 = {"right" : {"type": ["org.accordproject.ergo.Error"], "data": {"message": "Enforce condition failed"}}};
        } else {
          var vp2 = deref(unbrand(vlcontract), "date");
          var vp1 = "17 May 2018 13:53:33 EST";
          var vp1 = dateTimeFromString(vp1);
          var vnumberOfDays_0 = dateTimeDurationBetween(vp1, vp2);
          var t3;
          if (!(!((compare(vnumberOfDays_0,0.0) < 0)))) {
            t3 = {"right" : {"type": ["org.accordproject.ergo.Error"], "data": {"message": "Enforce condition failed"}}};
          } else {
            var vnumberOfDays = vnumberOfDays_0;
            var vannualInterest = deref(unbrand(vlcontract), "interestRate");
            var vcompounded = (voutstanding * Math.pow((1.0 + vannualInterest), (vnumberOfDays / 365.0)));
            var vX$match0 = deref(unbrand(vlcontract), "interestRate");
            var res1 = null;
            if (either(vX$match0)) {
              var vX$case0 = null;
              vX$case0 = toLeft(vX$match0);
              res1 = {"left" : {"$option": vX$case0}};
            } else {
              var vX$case1 = null;
              vX$case1 = toRight(vX$match0);
              res1 = {"right" : null};
            }
            var res2 = null;
            if (either(res1)) {
              var vX$case0_0 = null;
              vX$case0_0 = toLeft(res1);
              var vX$case0 = vX$case0_0;
              var vX$option = deref(vX$case0, "$option");
              res2 = vX$option;
            } else {
              var vX$case1 = null;
              vX$case1 = toRight(res1);
              res2 = 3.4;
            }
            t3 = {"left" : concat({"emit": vlemit}, concat({"state": vlstate}, {"response": brand(["org.accordproject.promissorynote.Response"],concat({"rate": res2}, {"outstandingBalance": vcompounded}))}))};
          }
          t4 = t3;
        }
        t5 = t4;
      }
      t6 = t5;
    }
    return t6;
  }
}

/*eslint-enable no-unused-vars*/
/*eslint-enable no-undef*/

