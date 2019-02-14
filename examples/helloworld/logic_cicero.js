/* Generated using ergoc version 0.6.2 */
'use strict';
/*eslint-disable no-unused-vars*/
/*eslint-disable no-undef*/
/*eslint-disable no-var*/


/**
 * Execute the smart clause
 * @param {Context} context - the Accord context
 * @param {org.accordproject.helloworld.Request} context.request - the incoming request
 * @param {org.accordproject.helloworld.Response} context.response - the response
 * @param {org.accordproject.base.Event} context.emit - the emitted events
 * @param {org.accordproject.cicero.contract.AccordContractState} context.state - the state
 * @AccordClauseLogic
 */
function orgXaccordprojectXhelloworldXHelloWorld_helloworld(context) {
  let pcontext = { 'request' : serializer.toJSON(context.request,{permitResourcesForRelationships:true}), 'state': serializer.toJSON(context.state,{permitResourcesForRelationships:true}), 'contract': serializer.toJSON(context.contract,{permitResourcesForRelationships:true}), 'emit': context.emit, 'now': context.now};
  //logger.info('ergo context: '+JSON.stringify(pcontext))
  let result = new orgXaccordprojectXhelloworldXHelloWorld().helloworld(pcontext);
  if (result.hasOwnProperty('left')) {
    //logger.info('ergo result: '+JSON.stringify(result))
    context.response = serializer.fromJSON(result.left.response, {validate: false, acceptResourcesForRelationships: true},{permitResourcesForRelationships:true});
    context.state = serializer.fromJSON(result.left.state, {validate: false, acceptResourcesForRelationships: true});
    let emitResult = [];
    for (let i = 0; i < result.left.emit.length; i++) {
      emitResult.push(serializer.fromJSON(result.left.emit[i], {validate: false, acceptResourcesForRelationships: true}));
    }
    context.emit = emitResult;
    return context;
  } else {
    throw new Error(result.right.message);
  }
}
class orgXaccordprojectXhelloworldXHelloWorld {
  main(context) {
    var vcontract = deref(context, "contract");
    var vnow = deref(context, "now");
    var vrequest = deref(context, "request");
    var vemit = deref(context, "emit");
    var vstate = deref(context, "state");
    var vlstate_0 = vstate;
    var vlemit_0 = vemit;
    var vX$match0 = vrequest;
    var res1 = null;
    if (either(cast(["org.accordproject.helloworld.Request"],vX$match0))) {
      var vX$case0 = null;
      vX$case0 = toLeft(cast(["org.accordproject.helloworld.Request"],vX$match0));
      res1 = {"left" : {"$main": vX$case0}};
    } else {
      var vX$case1 = null;
      vX$case1 = toRight(cast(["org.accordproject.helloworld.Request"],vX$match0));
      res1 = {"right" : null};
    }
    var res2 = null;
    if (either(res1)) {
      var vX$case0_0 = null;
      vX$case0_0 = toLeft(res1);
      var vX$0 = vX$case0_0;
      var vX$main = deref(vX$0, "$main");
      var vnow_0 = vnow;
      var vcontract_0 = vcontract;
      var vstate_0 = vlstate_0;
      var vemit_0 = vlemit_0;
      var vrequest_0 = vX$main;
      var vlstate = vstate;
      var vlemit = vemit;
      res2 = {"left" : concat(concat({"response": brand(["org.accordproject.helloworld.Response"],{"output": (((("Hello " + deref(unbrand(vcontract), "name")) + " (") + deref(unbrand(vrequest), "input")) + ")")})}, {"state": vlstate}), {"emit": vlemit})};
    } else {
      var vX$1 = null;
      vX$1 = toRight(res1);
      res2 = {"right" : {"type": ["org.accordproject.ergo.stdlib.ErgoErrorResponse"], "data": {"message": "DefaultMatch Error at 16:0-21:1 ''"}}};
    }
    return res2;
  }
  init(context) {
    var vemit = deref(context, "emit");
    var vstate = deref(context, "state");
    var vlstate_0 = vstate;
    var vlemit = vemit;
    var vlstate = brand(["org.accordproject.cicero.contract.AccordContractState"],{"stateId": "1"});
    return {"left" : concat(concat({"response": null}, {"state": vlstate}), {"emit": vlemit})};
  }
  helloworld(context) {
    var vrequest = deref(context, "request");
    var vcontract = deref(context, "contract");
    var vemit = deref(context, "emit");
    var vstate = deref(context, "state");
    var vlstate = vstate;
    var vlemit = vemit;
    return {"left" : concat(concat({"response": brand(["org.accordproject.helloworld.Response"],{"output": (((("Hello " + deref(unbrand(vcontract), "name")) + " (") + deref(unbrand(vrequest), "input")) + ")")})}, {"state": vlstate}), {"emit": vlemit})};
  }
}
const contract = new orgXaccordprojectXhelloworldXHelloWorld();
function dispatch(context) {
  return contract.main(context);
}
function init(context) {
  return contract.init(context);
}

/*eslint-enable no-unused-vars*/
/*eslint-enable no-undef*/

