/////////////////////////
// EJson Data Encoding //
/////////////////////////

class EjValue {}

function cast<T>(x : EjValue): T {
  if (x instanceof T) {
    let r : T = changetype<T>(x);
    return r;
  }
  return unreachable();
}

export class EjNull extends EjValue {
  constructor() { super(); }
}
export const IdEjNull = idof<EjNull>()

const c_null = new EjNull();

export class EjBool extends EjValue {
  value: bool
  constructor(a: bool) { super(); this.value = a; }
}
export const IdEjBool = idof<EjBool>()

const c_true = new EjBool(true);
const c_false = new EjBool(false);

export class EjNumber extends EjValue {
  value: f64
  constructor(a: f64) { super(); this.value = a; }
}
export const IdEjNumber = idof<EjNumber>()

const c_neg1 = new EjNumber(-1);
const c_1 = new EjNumber(1);
const c_0 = new EjNumber(0);

export class EjBigInt extends EjValue {
  value: i64
  constructor(a: i64) { super(); this.value = a; }
}
export const IdEjBigInt = idof<EjBigInt>()
export function ejBigInt_of_f64(x: f64) : EjBigInt {
  let i = I64.parseInt(Math.trunc(x).toString());
  return new EjBigInt(i);
}

export class EjString extends EjValue {
  value: string
  constructor(a: string) { super(); this.value = a; }
}
export const IdEjString = idof<EjString>()

export class EjStringBuilderUTF8 {
  private buf: Uint8Array
  private pos: i32
  constructor(n: i32) {
    this.pos = 0;
    this.buf = new Uint8Array(n);
  }
  putByte(val: u8): void {
    this.buf[this.pos] = val;
    this.pos++;
  }
  finalize(): EjString {
    let str = String.UTF8.decode(this.buf.buffer);
    return new EjString(str);
  }
}

export class EjArray extends EjValue {
  values: Array<EjValue>
  constructor(a: Array<EjValue>) { super(); this.values = a; }
}
export const IdArrayEjValue = idof<Array<EjValue>>()
export const IdEjArray = idof<EjArray>()

export class EjArrayBuilder {
  private arr: Array<EjValue>
  private pos: i32
  constructor(n: i32) {
    this.pos = 0;
    this.arr = new Array<EjValue>(n);
  }
  put(val: EjValue): EjArrayBuilder {
    this.arr[this.pos] = val;
    this.pos++;
    return this;
  }
  finalize(): EjArray {
    return new EjArray(this.arr)
  }
}

export class EjObject extends EjValue {
  values: Map<string, EjValue>
  constructor() { super(); this.values = new Map<string, EjValue>(); }
  has(k: EjString): bool {
    return this.values.has(k.value);
  }
  set(k: EjString, v: EjValue): EjObject {
    this.values.set(k.value, v);
    return this;
  }
  get(k: EjString): EjValue {
    // redundant debugging code unreachable
    // for a valid combination of engine, runtime, and compiled ergo
    if (! this.has(k)) {
      throw new Error("EjObject misses key '" + k.value + "'");
    }
    // actual code
    return this.values.get(k.value);
  }
  keys(): Array<EjString> {
    return this.values.keys().map<EjString>(x => new EjString(x));
  }
}
export const IdEjObject = idof<EjObject>()

/////////////////////////
// EJson Serialization //
/////////////////////////

class BytesBuilder {
  segments: Array<ArrayBuffer>
  size: i32

  constructor() { this.segments = []; this.size = 0; }

  append(s: ArrayBuffer): void {
    this.segments.push(s);
    this.size += s.byteLength;
  }

  finalize(): ArrayBuffer {
    let b = new ArrayBuffer(this.size);
    let p : i32 = 0;
    let v = Uint8Array.wrap(b);
    for (let i = 0; i < this.segments.length; i++) {
      let s = Uint8Array.wrap(this.segments[i]);
      // this is byte-by-byte copy. Could be much faster when copying words.
      for (let j = 0; j < s.length; j++) {
        v[p] = s[j];
        p++;
      }
    }
    return b;
  }
}

function ejson_to_bytes_(b: BytesBuilder, x:EjValue): void {
  if (x instanceof EjNull) {
    let s = new ArrayBuffer(1);
    Uint8Array.wrap(s)[0] = 0; // tag
    b.append(s);
    return;
  }
  if (x instanceof EjBool) {
    let xx : EjBool = changetype<EjBool>(x) ;
    let s = new ArrayBuffer(1);
    Uint8Array.wrap(s)[0] = xx.value ? 2 : 1; // tag
    b.append(s);
    return;
  }
  if (x instanceof EjNumber) {
    let xx : EjNumber = changetype<EjNumber>(x) ;
    let s = new ArrayBuffer(9);
    let v = new DataView(s);
    v.setUint8(0, 3);
    v.setFloat64(1, xx.value, true);
    b.append(s);
    return;
  }
  if (x instanceof EjBigInt) {
    let xx : EjBigInt = changetype<EjBigInt>(x) ;
    let s = new ArrayBuffer(9);
    let v = new DataView(s);
    v.setUint8(0, 4); // tag
    v.setInt64(1, xx.value, true);
    b.append(s);
    return;
  }
  if (x instanceof EjString) {
    let xx : EjString = changetype<EjString>(x) ;
    let utf8 = String.UTF8.encode(xx.value);
    let s = new Uint8Array(5);
    let v = new DataView(s.buffer);
    s[0] = 5; // tag
    v.setUint32(1, utf8.byteLength, true);
    b.append(s.buffer);
    b.append(utf8);
    return;
  }
  if (x instanceof EjArray) {
    let xx : EjArray = changetype<EjArray>(x) ;
    let s = new Uint8Array(5);
    let v = new DataView(s.buffer);
    s[0] = 6; // tag
    v.setUint32(1, xx.values.length, true);
    b.append(s.buffer);
    for (let i = 0; i < xx.values.length; i++) {
      ejson_to_bytes_(b, xx.values[i]);
    }
    return;
  }
  if (x instanceof EjObject) {
    let xx : EjObject = changetype<EjObject>(x) ;
    let s = new Uint8Array(5);
    let v = new DataView(s.buffer);
    s[0] = 7; // tag
    v.setUint32(1, xx.values.size, true);
    b.append(s.buffer);
    let keys = xx.values.keys();
    for (let i = 0; i < xx.values.size; i++) {
      let k = keys[i];
      // write key as utf8 string with byte length prefix
      let utf8 = String.UTF8.encode(k);
      let s = new Uint8Array(4);
      let v = new DataView(s.buffer);
      v.setUint32(0, utf8.byteLength, true);
      b.append(s.buffer);
      b.append(utf8);
      // write value
      ejson_to_bytes_(b, xx.values.get(k));
    }
    return;
  }
  unreachable();
}

export function alloc_bytes(n: i32): ArrayBuffer {
  return new ArrayBuffer(((n + 7) >> 3) << 3);
}

export function bytes_set_i64(b: ArrayBuffer, offset: i32, value: i64): void {
  Int64Array.wrap(b)[offset >> 3] = value;
}

export function ejson_to_bytes(x: EjValue): ArrayBuffer {
  let b = new BytesBuilder();
  ejson_to_bytes_(b, x);
  return b.finalize();
}

class MovingPointer {
  value: i32
  constructor(x: i32) { this.value = x }
  advance(by: i32): i32 {
    let r = this.value;
    this.value += by;
    return r;
  }
}

function ejson_of_bytes_(p: MovingPointer, b:ArrayBuffer): EjValue {
  // switch tag
  switch(Uint8Array.wrap(b, p.advance(1), 1)[0]) {
    case 0:
      return c_null;
    case 1:
      return c_false;
    case 2:
      return c_true;
    case 3: {
      let v = new DataView(b, p.advance(8), 8);
      return new EjNumber(v.getFloat64(0, true));
    }
    case 4: {
      let v = new DataView(b, p.advance(8), 8);
      return new EjBigInt(v.getInt64(0, true));
    }
    case 5: {
      let v = new DataView(b, p.advance(4), 4);
      let len = v.getUint32(0, true);
      // ArrayBuffer is a pointer
      let str = String.UTF8.decodeUnsafe(changetype<i32>(b) + p.advance(len), len);
      return new EjString(str);
    }
    case 6: {
      let v = new DataView(b, p.advance(4), 4)
      let len = v.getUint32(0, true);
      let arr = new Array<EjValue>(len);
      for (let i=<u32>0; i < len; i++) {
        arr[i] = ejson_of_bytes_(p, b);
      }
      return new EjArray(arr);
    }
    case 7: {
      let v = new DataView(b, p.advance(4), 4)
      let len = v.getUint32(0, true);
      let obj = new EjObject();
      for (let i=<u32>0; i < len; i++) {
        let v = new DataView(b, p.advance(4), 4);
        let key_len = v.getUint32(0, true);
        let key = String.UTF8.decodeUnsafe(changetype<i32>(b) + p.advance(key_len), key_len);
        let val = ejson_of_bytes_(p, b);
        obj.set(new EjString(key), val);
      }
      return obj;
    }
  }
  return unreachable();
}

export function ejson_of_bytes(b: ArrayBuffer): EjValue {
  return ejson_of_bytes_(new MovingPointer(0), b);
}

/////////////////////
// EJson Operators //
/////////////////////

export function opNot(a: EjBool): EjBool {
  return new EjBool(!a.value);
}

export function opNeg(a: EjNumber): EjNumber {
  return new EjNumber(-a.value);
}

export function opAnd(a: EjBool, b: EjBool): EjBool {
  return new EjBool(a.value && b.value);
}

export function opOr(a: EjBool, b: EjBool): EjBool {
  return new EjBool(a.value || b.value);
}

export function opLt(a: EjNumber, b: EjNumber): EjBool {
  return new EjBool(a.value < b.value);
}

export function opLe(a: EjNumber, b: EjNumber): EjBool {
  return new EjBool(a.value <= b.value);
}

export function opGt(a: EjNumber, b: EjNumber): EjBool {
  return new EjBool(a.value > b.value);
}

export function opGe(a: EjNumber, b: EjNumber): EjBool {
  return new EjBool(a.value >= b.value);
}

export function opAddString(a: EjString, b: EjString): EjString {
  return new EjString(a.value + b.value);
}

export function opAddNumber(a: EjNumber, b: EjNumber): EjNumber {
  return new EjNumber(a.value + b.value);
}

export function opSub(a: EjNumber, b: EjNumber): EjNumber {
  return new EjNumber(a.value - b.value);
}

export function opMult(a: EjNumber, b: EjNumber): EjNumber {
  return new EjNumber(a.value * b.value);
}

export function opDiv(a: EjNumber, b: EjNumber): EjNumber {
  return new EjNumber(a.value / b.value);
}

export function opStrictEqual(a: EjValue, b: EjValue): EjBool {
  if (a instanceof EjNull && b instanceof EjNull) {
    return c_true;
  }
  if (a instanceof EjBool && b instanceof EjBool) {
    let aa : EjBool = changetype<EjBool>(a) ;
    let bb : EjBool = changetype<EjBool>(b) ;
    return aa.value == bb.value ? c_true : c_false;
  }
  if (a instanceof EjNumber && b instanceof EjNumber) {
    let aa : EjNumber = changetype<EjNumber>(a) ;
    let bb : EjNumber = changetype<EjNumber>(b) ;
    return aa.value == bb.value ? c_true : c_false;
  }
  if (a instanceof EjString && b instanceof EjString) {
    let aa : EjString = changetype<EjString>(a) ;
    let bb : EjString = changetype<EjString>(b) ;
    return aa.value == bb.value ? c_true : c_false;
  }
  return unreachable();
}

export function opStrictDisEqual(a: EjValue, b: EjValue): EjBool {
  if (a instanceof EjNull && b instanceof EjNull) {
    return c_false;
  }
  if (a instanceof EjBool && b instanceof EjBool) {
    let aa : EjBool = changetype<EjBool>(a) ;
    let bb : EjBool = changetype<EjBool>(b) ;
    return aa.value != bb.value ? c_true : c_false;
  }
  if (a instanceof EjNumber && b instanceof EjNumber) {
    let aa : EjNumber = changetype<EjNumber>(a) ;
    let bb : EjNumber = changetype<EjNumber>(b) ;
    return aa.value != bb.value ? c_true : c_false;
  }
  if (a instanceof EjString && b instanceof EjString) {
    let aa : EjString = changetype<EjString>(a) ;
    let bb : EjString = changetype<EjString>(b) ;
    return aa.value != bb.value ? c_true : c_false;
  }
  return unreachable();
}

export function opArray(a: EjValue): EjArray {
  // TODO: opArray
  return unreachable();
}

export function opArrayLength(a: EjArray): EjBigInt {
  return new EjBigInt(a.values.length);
}

export function opArrayPush(a: EjArray, b: EjValue): EjArray {
  // TODO: opArrayPush: should we mutate the array?;
  return new EjArray(a.values.concat([b]));
}

export function opArrayAccess(a: EjArray, b: EjBigInt): EjValue {
  // TODO: opArrayAccess: should we check out of bound and i32 overflow?
  return a.values[i32(b.value)];
}

export function opObject(a: EjValue): EjObject {
  // TODO: opObject
  return unreachable();
}

export function opAccess(a: EjObject, k: EjString): EjValue {
  // TODO: opAccess redundant with runtimeRecDot?
  // TODO: opAccess: check for key not found needed?
  return a.get(k);
}

export function opHasOwnProperty(a: EjObject, k: EjString): EjValue {
  // TODO: opHasOwnProperty
  return unreachable();
}

export function opMathMin(a: EjNumber, b: EjNumber): EjNumber {
  return new EjNumber(Math.min(a.value, b.value));
}

export function opMathMax(a: EjNumber, b: EjNumber): EjNumber {
  return new EjNumber(Math.max(a.value, b.value));
}

export function opMathExp(a: EjNumber): EjNumber {
  return new EjNumber(Math.exp(a.value));
}

export function opMathPow(a: EjNumber, b: EjNumber): EjNumber {
  return new EjNumber(Math.pow(a.value, b.value));
}

export function opMathAbs(a: EjNumber): EjNumber {
  return new EjNumber(Math.abs(a.value));
}

export function opMathLog(a: EjNumber): EjNumber {
  return new EjNumber(Math.log(a.value));
}

export function opMathLog10(a: EjNumber): EjNumber {
  return new EjNumber(Math.log10(a.value));
}

export function opMathSqrt(a: EjNumber): EjNumber {
  return new EjNumber(Math.sqrt(a.value));
}

export function opMathCeil(a: EjNumber): EjNumber {
  return new EjNumber(Math.ceil(a.value));
}

export function opMathFloor(a: EjNumber): EjNumber {
  return new EjNumber(Math.floor(a.value));
}

export function opMathTrunc(a: EjNumber): EjNumber {
  return new EjNumber(Math.trunc(a.value));
}

/////////////////////////////
// EJson Runtime Operators //
/////////////////////////////

export function runtimeEqual(a: EjValue, b: EjValue): EjBool {
  if (a instanceof EjNull && b instanceof EjNull) {
    return c_true;
  }
  if (a instanceof EjBool && b instanceof EjBool) {
    let aa : EjBool = changetype<EjBool>(a) ;
    let bb : EjBool = changetype<EjBool>(b) ;
    return aa.value == bb.value ? c_true : c_false;
  }
  if (a instanceof EjNumber && b instanceof EjNumber) {
    let aa : EjNumber = changetype<EjNumber>(a) ;
    let bb : EjNumber = changetype<EjNumber>(b) ;
    return aa.value == bb.value ? c_true : c_false;
  }
  if (a instanceof EjBigInt && b instanceof EjBigInt) {
    let aa : EjBigInt = changetype<EjBigInt>(a) ;
    let bb : EjBigInt = changetype<EjBigInt>(b) ;
    return aa.value == bb.value ? c_true : c_false;
  }
  if (a instanceof EjString && b instanceof EjString) {
    let aa : EjString = changetype<EjString>(a) ;
    let bb : EjString = changetype<EjString>(b) ;
    return aa.value == bb.value ? c_true : c_false;
  }
  if (a instanceof EjArray && b instanceof EjArray) {
    let aa : EjArray = changetype<EjArray>(a) ;
    let bb : EjArray = changetype<EjArray>(b) ;
    if (aa.values.length != bb.values.length) {
      return c_false;
    }
    for (let i = 0; i < aa.values.length; i++) {
      if (! runtimeEqual(aa.values[i], bb.values[i]).value) {
        return c_false;
      }
    }
    return c_true;
  }
  if (a instanceof EjObject && b instanceof EjObject) {
    let aa : EjObject = changetype<EjObject>(a) ;
    let bb : EjObject = changetype<EjObject>(b) ;
    if (aa.values.size != bb.values.size) {
      return c_false;
    }
    let keys = aa.values.keys();
    for (let i = 0; i < keys.length; i++) {
      let k = keys[i];
      if (! bb.values.has(k) ||
          ! runtimeEqual(aa.values[k], bb.values[k]).value ) {
        return c_false;
      }
    }
    return c_true;
  }
  return c_false;
}

function compare<T>(a: T, b: T): EjNumber {
  if (a < b) { return c_neg1; }
  if (a > b) { return c_1; }
  return c_0;
}

export function runtimeCompare(a: EjValue, b: EjValue): EjNumber {
  if (a instanceof EjNumber && b instanceof EjNumber) {
    let aa : EjNumber = changetype<EjNumber>(a) ;
    let bb : EjNumber = changetype<EjNumber>(b) ;
    return compare<f64>(aa.value, bb.value);
  }
  if (a instanceof EjBigInt && b instanceof EjBigInt) {
    let aa : EjBigInt = changetype<EjBigInt>(a) ;
    let bb : EjBigInt = changetype<EjBigInt>(b) ;
    return compare<i64>(aa.value, bb.value);
  }
  return unreachable();
}

// TODO: recConcat which argument "wins" in case of a conflict?
export function runtimeRecConcat(a: EjObject, b:EjObject): EjObject {
  let r = new EjObject();
  let k = a.values.keys();
  for (let i = 0; i < k.length; i++) {
    r.values.set(k[i], a.values.get(k[i]));
  }
  k = b.values.keys();
  for (let i = 0; i < k.length; i++) {
    r.values.set(k[i], b.values.get(k[i]));
  }
  return r;
}

export function runtimeRecDot(a: EjObject, k:EjString): EjValue {
  // TODO: runtimeRecDot redundant with opAccess?
  // TODO: runtimeRecDot: check for key not found needed?
  return a.get(k);
}

export function runtimeArrayLength(a: EjArray) : EjBigInt {
  return new EjBigInt(a.values.length);
}

function ejObject(l: Array<Array<EjValue>>): EjObject {
  let obj = new EjObject();
  for (let i=0; i < l.length; i++) {
    obj.set(<EjString>l[i][0], l[i][1]);
  }
  return obj
}

const c_$left = new EjString("$left")
const c_$right = new EjString("$right")

function ejLeft(v: EjValue): EjObject {
  return ejObject([[c_$left, v]]);
}

function ejRight(v: EjValue): EjObject {
  return ejObject([[c_$right, v]]);
}

export function runtimeEither(a: EjObject): EjBool {
  if (a.has(c_$left)){
    return c_true;
  }
  if (a.has(c_$right)) {
    return c_false;
  }
  return unreachable();
}

export function runtimeToLeft(a: EjObject): EjValue {
  return runtimeRecDot(a, c_$left);
}

export function runtimeToRight(a: EjObject): EjValue {
  return runtimeRecDot(a, c_$right);
}

const c_$data = new EjString("$data")
const c_$class = new EjString("$class")
const c_none = ejRight(c_null)

export function runtimeUnbrand(a: EjObject): EjValue {
  return runtimeRecDot(a, c_$data);
}

export function runtimeCast(hierarchy: EjArray, brands: EjArray, x: EjObject) : EjValue {
  let from_brands = cast<EjArray>(runtimeRecDot(x, c_$class)).values;
  let to_brands = brands.values;
  let pairs = hierarchy.values;
  for (let i = 0; i < to_brands.length; i++) {
    let to_brand = cast<EjString>(to_brands[i]).value;
    let to_brand_ok = false;
    for (let j = 0; j < from_brands.length; j++) {
      let from_brand = cast<EjString>(from_brands[j]).value;
      if (to_brand == from_brand) {
        to_brand_ok = true;
        // break j loop
        j = I32.MAX_VALUE - 1;
      } else {
        for (let k = 0; k < pairs.length; k++) {
          let pair = cast<EjArray>(pairs[k]).values;
          assert(pair.length == 2);
          let sub = cast<EjString>(pair[0]).value;
          let sup = cast<EjString>(pair[1]).value;
          if (from_brand == sub && to_brand == sup) {
            to_brand_ok = true;
            // break j loop
            j = I32.MAX_VALUE - 1;
            k = I32.MAX_VALUE - 1;
          }
        }
      }
    }
    if (!to_brand_ok) {
      return c_none;
    }
  }
  // return re-branded object
  return ejLeft(
    ejObject(
      [[c_$class, brands],
       [c_$data, runtimeRecDot(x, c_$data)
    ]]));
}

export function runtimeNatLe(a: EjBigInt, b: EjBigInt): EjBool {
  return new EjBool(a.value <= b.value);
}

export function runtimeNatLt(a: EjBigInt, b: EjBigInt): EjBool {
  return new EjBool(a.value < b.value);
}

export function runtimeNatPlus(a: EjBigInt, b: EjBigInt): EjBigInt {
  return new EjBigInt(a.value + b.value);
}

export function runtimeFloatOfNat(a: EjBigInt): EjNumber {
  let s : string = a.value.toString();
  let x : f64 = F64.parseFloat(s);
  return new EjNumber(x);
}
