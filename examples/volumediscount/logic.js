'use strict';
/*eslint-disable no-unused-vars*/
/*eslint-disable no-undef*/
/*eslint-disable no-var*/


class VolumeDiscount {
  main(context) {
    var vemit = deref(context, "emit");
    var vstate = deref(context, "state");
    var vcontract = deref(context, "contract");
    var vrequest = deref(context, "request");
    var vlcontract_0 = vcontract;
    var vlstate_0 = vstate;
    var vlemit_0 = vemit;
    var vX$match0 = vrequest;
    var res3 = null;
    if (either(cast(["org.accordproject.volumediscount.VolumeDiscountRequest"],vX$match0))) {
      var vX$main = null;
      vX$main = toLeft(cast(["org.accordproject.volumediscount.VolumeDiscountRequest"],vX$match0));
      var vrequest_0 = vX$main;
      var vlcontract = vcontract;
      var vlstate = vstate;
      var vlemit = vemit;
      var t2;
      if ((compare(deref(unbrand(vrequest_0), "netAnnualChargeVolume"),deref(unbrand(vlcontract), "firstVolume")) < 0)) {
        t2 = {"left" : concat({"emit": vlemit}, concat({"state": vlstate}, {"response": brand(["org.accordproject.volumediscount.VolumeDiscountResponse"],{"discountRate": deref(unbrand(vlcontract), "firstRate")})}))};
      } else {
        var t1;
        if ((compare(deref(unbrand(vrequest_0), "netAnnualChargeVolume"),deref(unbrand(vlcontract), "secondVolume")) < 0)) {
          t1 = {"left" : concat({"emit": vlemit}, concat({"state": vlstate}, {"response": brand(["org.accordproject.volumediscount.VolumeDiscountResponse"],{"discountRate": deref(unbrand(vlcontract), "secondRate")})}))};
        } else {
          t1 = {"left" : concat({"emit": vlemit}, concat({"state": vlstate}, {"response": brand(["org.accordproject.volumediscount.VolumeDiscountResponse"],{"discountRate": deref(unbrand(vlcontract), "thirdRate")})}))};
        }
        t2 = t1;
      }
      res3 = t2;
    } else {
      var vX$case0 = null;
      vX$case0 = toRight(cast(["org.accordproject.volumediscount.VolumeDiscountRequest"],vX$match0));
      res3 = {"right" : brand(["org.accordproject.volumediscount.Error"],{"message": ""})};
    }
    return res3;
  }
  volumediscount(context) {
    var vrequest = deref(context, "request");
    var vemit = deref(context, "emit");
    var vstate = deref(context, "state");
    var vcontract = deref(context, "contract");
    var vlcontract = vcontract;
    var vlstate = vstate;
    var vlemit = vemit;
    var t2;
    if ((compare(deref(unbrand(vrequest), "netAnnualChargeVolume"),deref(unbrand(vlcontract), "firstVolume")) < 0)) {
      t2 = {"left" : concat({"emit": vlemit}, concat({"state": vlstate}, {"response": brand(["org.accordproject.volumediscount.VolumeDiscountResponse"],{"discountRate": deref(unbrand(vlcontract), "firstRate")})}))};
    } else {
      var t1;
      if ((compare(deref(unbrand(vrequest), "netAnnualChargeVolume"),deref(unbrand(vlcontract), "secondVolume")) < 0)) {
        t1 = {"left" : concat({"emit": vlemit}, concat({"state": vlstate}, {"response": brand(["org.accordproject.volumediscount.VolumeDiscountResponse"],{"discountRate": deref(unbrand(vlcontract), "secondRate")})}))};
      } else {
        t1 = {"left" : concat({"emit": vlemit}, concat({"state": vlstate}, {"response": brand(["org.accordproject.volumediscount.VolumeDiscountResponse"],{"discountRate": deref(unbrand(vlcontract), "thirdRate")})}))};
      }
      t2 = t1;
    }
    return t2;
  }
}

/*eslint-enable no-unused-vars*/
/*eslint-enable no-undef*/

