const loader = require("@assemblyscript/loader");
const should = require('chai').should();
const assert = require('chai').assert;
const fs = require('fs');
const enc = require('../lib/runtime_encoding.js');
const bin = require('../lib/binary_encoding.js');

function writeString(module, str) {
  return m.exports.__retain(m.exports.__allocString(aStr));
}

const values = [
  null,
  Math.PI,
  1,
  0,
  true,
  false,
  "",
  "Hello World!",
  "hello world!",
  {'$left': 1},
  {'$right': 1},
  // {'$nat': "1"},
  // {'$nat': "1000"},
  [],
  [1],
  ["", ""],
  ["", null],
  {},
  {a : null},
  {a : false},
  {a : [], b: 0}
]

describe('AssemblyScript: Ejson operators', function () {
  it('low-level write/read roundtrip', async function () {
    // Manual read/write. Do not read as example.
    let m = await loader.instantiate(fs.readFileSync("build/untouched.wasm"));
    let t = new m.exports.EjBool(true);
    let f = new m.exports.EjBool(false);
    let pi = new m.exports.EjNumber(Math.PI);
    t.value.should.equal(1);
    f.value.should.equal(0);
    pi.value.should.equal(Math.PI);
    // Strings require some effort.
    let hello_p = m.exports.__retain(m.exports.__allocString("Hello World!"));
    let hello = new m.exports.EjString(hello_p);
    m.exports.__release(hello_p);
    let val_p = hello.value;
    m.exports.__release(hello);
    m.exports.__getString(val_p).should.equal("Hello World!");
    m.exports.__release(val_p);
  });
  it('operator PoC', async function () {
    // Manual read/write. Do not read as example.
    let m = await loader.instantiate(fs.readFileSync("build/untouched.wasm"));
    let { __release, EjBool, opOr, opNot } = m.exports;
    let t = new EjBool(true);
    let f = new EjBool(false);
    let res = opNot(opOr(t, f));
    __release(t);
    __release(f);
    EjBool.wrap(res).value.should.equal(0);
    __release(res);
  });
  it('runtime encoding write', async function () {
    // Manual read. Do not read as example.
    let m = await loader.instantiate(fs.readFileSync("build/untouched.wasm"));
    let t = enc.write(m, true);
    let f = enc.write(m, false)
    let pi = enc.write(m, Math.PI);
    t.value.should.equal(1);
    f.value.should.equal(0);
    pi.value.should.equal(Math.PI);
    let hello = enc.write(m, "Hello World!");
    let val_p = hello.value;
    m.exports.__release(hello);
    m.exports.__getString(val_p).should.equal("Hello World!");
    m.exports.__release(val_p);
  });
  it('runtime encoding read', async function () {
    // Manual write. Do not read as example.
    let m = await loader.instantiate(fs.readFileSync("build/untouched.wasm"));
    let n = new m.exports.EjNull();
    should.equal(enc.read(m, n), null);
    let t = new m.exports.EjBool(true);
    let f = new m.exports.EjBool(false);
    let pi = new m.exports.EjNumber(Math.PI);
    enc.read(m, t).should.equal(true);
    enc.read(m, f).should.equal(false);
    enc.read(m, pi).should.equal(Math.PI);
    // Strings require some effort.
    let hello_p = m.exports.__retain(m.exports.__allocString("Hello World!"));
    let hello = new m.exports.EjString(hello_p);
    m.exports.__release(hello_p);
    enc.read(m, hello).should.equal("Hello World!");
    let val_p = hello.value;
    m.exports.__release(hello);
    m.exports.__getString(val_p).should.equal("Hello World!");
    m.exports.__release(val_p);
  });
  it('runtime encoding read/write roundtrip', async function () {
    let m = await loader.instantiate(fs.readFileSync("build/untouched.wasm"));
    let t = enc.write(m, true);
    let f = enc.write(m, false)
    let pi = enc.write(m, Math.PI);
    let hello = enc.write(m, "Hello World!");
    enc.read(m, t).should.equal(true);
    enc.read(m, f).should.equal(false);
    enc.read(m, pi).should.equal(Math.PI);
    enc.read(m, hello).should.equal("Hello World!");
    // Arrays
    let a0 = [1,2,3];
    let a1 = [];
    let a2 = ['a', "abc", 1, null];
    enc.read(m, enc.write(m, a0)).should.deep.equal(a0);
    enc.read(m, enc.write(m, a1)).should.deep.equal(a1);
    enc.read(m, enc.write(m, a2)).should.deep.equal(a2);
    // Objects
    let o0 = { a: 'a', b: 'b' };
    let o1 = {};
    let o2 = {'null': null, arr: [a0, a1, a2], pi: Math.PI};
    enc.read(m, enc.write(m, o0)).should.deep.equal(o0);
    enc.read(m, enc.write(m, o1)).should.deep.equal(o1);
    enc.read(m, enc.write(m, o2)).should.deep.equal(o2);
  });
  it('runtimeEqual', async function () {
    let m = await loader.instantiate(fs.readFileSync("build/untouched.wasm"));
    let ptra = values.map(x => enc.write(m, x));
    let ptrb = values.map(x => enc.write(m, x));
    let str = JSON.stringify;
    for(let i = 0; i < ptra.length; i++) {
      for(let j = 0; j < ptrb.length; j++) {
        assert((i == j) == enc.read(m, m.exports.runtimeEqual(ptra[i], ptrb[j])),
        `Unexpected result on ${str(values[i])} == ${str(values[j])}`);
      }
    }
  });
  it('runtimeCompare', async function () {
    let m = await loader.instantiate(fs.readFileSync("build/untouched.wasm"));
    let na = enc.write(m, 12);
    let nb = enc.write(m, 13);
    assert(enc.read(m, m.exports.runtimeCompare(na, na)) ==  0, '=');
    assert(enc.read(m, m.exports.runtimeCompare(na, nb)) == -1, '<');
    assert(enc.read(m, m.exports.runtimeCompare(nb, nb)) ==  0, '=');
    assert(enc.read(m, m.exports.runtimeCompare(nb, na)) ==  1, '>');
    let bia = enc.write(m, {'$nat': "12"});
    let bib = enc.write(m, {'$nat': "13"});
    assert(enc.read(m, m.exports.runtimeCompare(bia, bia)) ==  0, '=');
    assert(enc.read(m, m.exports.runtimeCompare(bia, bib)) == -1, '<');
    assert(enc.read(m, m.exports.runtimeCompare(bib, bib)) ==  0, '=');
    assert(enc.read(m, m.exports.runtimeCompare(bib, bia)) ==  1, '>');
  });
  it('runtimeRecConcat / Dot', async function () {
    let m = await loader.instantiate(fs.readFileSync("build/untouched.wasm"));
    let { runtimeRecConcat, runtimeRecDot } = m.exports;
    let a = enc.write(m, {a: 1});
    let b = enc.write(m, {b: 2});
    let ab = runtimeRecConcat(a,b);
    let ka = enc.write(m, 'a');
    let kb = enc.write(m, 'b');
    assert(enc.read(m, runtimeRecDot(ab,ka)) ==  1, 'a == 1');
    assert(enc.read(m, runtimeRecDot(ab,kb)) ==  2, 'b == 2');
  });
  it('runtimeEither / ToLeft / ToRight', async function () {
    let m = await loader.instantiate(fs.readFileSync("build/untouched.wasm"));
    let { runtimeEither, runtimeToLeft, runtimeToRight } = m.exports;
    let l = enc.write(m, {$left: 1});
    let r = enc.write(m, {$right: 2});
    assert(enc.read(m, runtimeEither(l)), 'either / left');
    assert(! enc.read(m, runtimeEither(r)), 'either / right');
    assert(enc.read(m, runtimeToLeft(l)) == 1, 'toLeft');
    assert(enc.read(m, runtimeToRight(r)) == 2, 'toRight');
  });
});

describe('AssemblyScript: EJson encodings', function () {
  it('js -> runtime -> binary -> runtime -> js', async function () {
    let m = await loader.instantiate(fs.readFileSync("build/untouched.wasm"));
    let { ejson_to_bytes, ejson_of_bytes } = m.exports;
    function t(x, label) {
      assert.deepEqual(enc.read(m, ejson_of_bytes(ejson_to_bytes(enc.write(m,x)))), x , label);
    }
    t(null, 'null');
    t(true, 'true');
    t(false, 'false');
    t(3.14, '3.14');
    t({$nat: 42}, '{$nat: 42}');
    t({$left: true}, '{$left: true}');
    t({$right: true}, '{$right: true}');
    t('', 'empty string');
    t('Hello World!', 'Hello World!');
    t([], 'empty array');
    t([1,2,3,null,false,true], 'non-empty array');
    t({}, 'empty object');
    t({a: 1, b: 2, '!': null}, 'non-empty object');
  });
  it('js -> binary -> runtime -> js', async function () {
    let m = await loader.instantiate(fs.readFileSync("build/untouched.wasm"));
    let { __alloc, ejson_of_bytes, memory } = m.exports;
    function t(x, label) {
      let x_bin = Buffer.from(bin.ejson_to_bytes(x));
      let x_bin_ptr = __alloc(x_bin.byteLength, 0);
      x_bin.copy(Buffer.from(memory.buffer, x_bin_ptr));
      let x_ptr = ejson_of_bytes(x_bin_ptr);
      assert.deepEqual(enc.read(m, x_ptr), x, label);
    }
    t(null, 'null');
    t(true, 'true');
    t(false, 'false');
    t(3.14, '3.14');
    t({$nat: 42}, '{$nat: 42}');
    t('', 'empty string');
    t([], 'empty array');
    t([1,2,3,null,false,true], 'non-empty array');
    t({}, 'empty object');
    t('Hello World!', 'Hello World!');
    t({a: 1, b: 2, '!': null}, 'non-empty object');
    t({}, 'empty object');
    t({a: 1, b: 2, '!': null}, 'non-empty object');
    t({$left: true}, '{$left: true}');
    t({$right: true}, '{$right: true}');
  });
  it('js -> runtime -> binary -> js', async function () {
    let m = await loader.instantiate(fs.readFileSync("build/untouched.wasm"));
    let { __alloc, ejson_to_bytes, memory } = m.exports;
    function t(x, label) {
      let x_bin_ptr = ejson_to_bytes(enc.write(m,x));
      let x_from_bin = bin.ejson_of_bytes(memory.buffer, x_bin_ptr);
      assert.deepEqual(x, x_from_bin, label);
    }
    t(null, 'null');
    t(true, 'true');
    t(false, 'false');
    t(3.14, '3.14');
    t({$nat: 42}, '{$nat: 42}');
    t('', 'empty string');
    t([], 'empty array');
    t([1,2,3,null,false,true], 'non-empty array');
    t({}, 'empty object');
    t('Hello World!', 'Hello World!');
    t({a: 1, b: 2, '!': null}, 'non-empty object');
    t({}, 'empty object');
    t({a: 1, b: 2, '!': null}, 'non-empty object');
    t({$left: true}, '{$left: true}');
    t({$right: true}, '{$right: true}');
  });
  it('js -> binary -> js', async function () {
    function t(x, label) {
      let x_bin = bin.ejson_to_bytes(x);
      let y = bin.ejson_of_bytes(x_bin, 0);
      assert.deepEqual(x, y, label);
    }
    t(null, 'null');
    t(true, 'true');
    t(false, 'false');
    t(3.14, '3.14');
    t({$nat: 42}, '{$nat: 42}');
    t('', 'empty string');
    t([], 'empty array');
    t([1,2,3,null,false,true], 'non-empty array');
    t({}, 'empty object');
    t('Hello World!', 'Hello World!');
    t({a: 1, b: 2, '!': null}, 'non-empty object');
    t({}, 'empty object');
    t({a: 1, b: 2, '!': null}, 'non-empty object');
    t({$left: true}, '{$left: true}');
    t({$right: true}, '{$right: true}');
  });
});
