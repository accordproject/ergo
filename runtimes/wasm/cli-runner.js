'use strict';

const fs = require('fs');
const engine = require('./lib/engine.js');

async function main(runtime, module, schema, input, expected) {
  console.log("invoke:");
  console.log({runtime, module, input, expected});
  let rt = fs.readFileSync(runtime);
  let mod = fs.readFileSync(module);
  let scm = JSON.parse(fs.readFileSync(schema));
  let hierarchy = scm ? scm.inheritance.map(x => [x.sub, x.sup]) : [];
  console.log("inheritance:");
  console.log(hierarchy);
  let arg = JSON.parse(fs.readFileSync(input));
  console.log("input:");
  console.log(arg);
  let exp = JSON.parse(fs.readFileSync(expected));
  console.log("expected:");
  console.log(JSON.stringify(exp, null, 2));
  let res = await engine.invoke(rt, mod, "qcert_main", hierarchy, arg);
  console.log("output:");
  console.log(JSON.stringify(res, null, 2));
}

const rt = process.argv[2];
const mod = process.argv[3];
const schema = process.argv[4];
const arg = process.argv[5];
const exp = process.argv[6];

main(rt, mod, schema, arg, exp);
