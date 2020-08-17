'use strict';

const loader = require("@assemblyscript/loader");
const bin = require('./binary_encoding.js');

function write(mod, value) {
  let { __alloc, __retain, __release, ejson_of_bytes, memory} = mod.exports;
  let value_bin = bin.ejson_to_bytes(value); // ejson --JS--> binary
  let bytes_ptr = __retain(__alloc(value_bin.byteLength)); // alloc runtime memory
  Buffer.from(value_bin).copy(Buffer.from(memory.buffer, bytes_ptr)); // copy binary value
  return bytes_ptr;
}

function read(mod, ptr) {
  let { memory, ejson_to_bytes } = mod.exports;
  let value = bin.ejson_of_bytes(memory.buffer, ptr); // binary --JS--> ejson
  return value;
}

async function invoke(runtime, module, fn_name, hierarchy, arg) {
  let rt = await loader.instantiate(runtime);
  let m = await loader.instantiate(module, { runtime: rt.instance.exports });
  let hierarchy_ptr = write(rt, hierarchy);
  let arg_ptr = write(rt, arg);
  let res_ptr = m.exports[fn_name](hierarchy_ptr, arg_ptr);
  let res = read(rt, res_ptr);
  return res;
}

module.exports = { invoke };
