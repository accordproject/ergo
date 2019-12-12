(* generated ocaml file *)
let accordproject = {xxx|
{"type":"Program","namespace":"org.accordproject.base","imports":[],"body":[{"type":"AssetDeclaration","id":{"type":"Identifier","name":"Asset"},"classExtension":null,"idField":null,"body":{"type":"ClassDeclarationBody","declarations":[],"location":{"start":{"offset":616,"line":16,"column":25},"end":{"offset":616,"line":16,"column":25}}},"abstract":["abstract",null],"decorators":[],"location":{"start":{"offset":592,"line":16,"column":1},"end":{"offset":617,"line":16,"column":26}}},{"type":"ParticipantDeclaration","id":{"type":"Identifier","name":"Participant"},"classExtension":null,"idField":null,"body":{"type":"ClassDeclarationBody","declarations":[],"location":{"start":{"offset":654,"line":17,"column":37},"end":{"offset":654,"line":17,"column":37}}},"abstract":["abstract",null],"decorators":[],"location":{"start":{"offset":618,"line":17,"column":1},"end":{"offset":655,"line":17,"column":38}}},{"type":"TransactionDeclaration","id":{"type":"Identifier","name":"Transaction"},"classExtension":null,"body":{"type":"ClassDeclarationBody","declarations":[],"location":{"start":{"offset":692,"line":18,"column":37},"end":{"offset":692,"line":18,"column":37}}},"idField":null,"abstract":["abstract",null],"decorators":[],"location":{"start":{"offset":656,"line":18,"column":1},"end":{"offset":693,"line":18,"column":38}}},{"type":"EventDeclaration","id":{"type":"Identifier","name":"Event"},"classExtension":null,"body":{"type":"ClassDeclarationBody","declarations":[],"location":{"start":{"offset":718,"line":19,"column":25},"end":{"offset":718,"line":19,"column":25}}},"idField":null,"abstract":["abstract",null],"decorators":[],"location":{"start":{"offset":694,"line":19,"column":1},"end":{"offset":719,"line":19,"column":26}}}]}|xxx}
let stdlib = {xxx|
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

namespace org.accordproject.ergo.stdlib

import org.accordproject.cicero.runtime.*

// Double operations
define function sqrt(x:Double) : Double
define function exp(x:Double) : Double
define function log(x:Double) : Double
define function log10(x:Double) : Double
define function ceil(x:Double) : Double
define function floor(x:Double) : Double
define function abs(x:Double) : Double
define function max(x:Double[]) : Double
define function min(x:Double[]) : Double
define function average(x:Double[]) : Double
define function sum(x:Double[]) : Double
define function doubleToInteger(x:Double) : Integer
define function doubleToLong(x:Double) : Long
define function truncate(x:Double) : Integer

define function maxPair(x:Double, y:Double) : Double
define function minPair(x:Double, y:Double) : Double

// Integer operations
define function integerAbs(x:Integer) : Integer
define function integerLog2(x:Integer) : Integer
define function integerSqrt(x:Integer) : Integer
define function integerToDouble(x:Integer) : Double

define function integerMin(x:Integer, y:Integer) : Integer
define function integerMax(x:Integer, y:Integer) : Integer
define function integerModulo(x:Integer, y:Integer) : Integer {
	let result = x % y;
	if result >= 0 then return result
	else return -result
}

// Long operations
define function longAbs(x:Long) : Long
define function longLog2(x:Long) : Long
define function longSqrt(x:Long) : Long
define function longToDouble(x:Long) : Double

define function longMin(x:Long, y:Long) : Long
define function longMax(x:Long, y:Long) : Long
define function longModulo(x:Long, y:Long) : Long {
	let result = x % y;
	if result >= 0 then return result
	else return -result
}

define constant maxPosInteger32 : Long =  doubleToLong(2.0 ^ 32.0 - 1.0)
define constant maxInteger32 : Long =  doubleToLong(2.0 ^ 31.0 - 1.0)
define constant minInteger32 : Long = doubleToLong(- 2.0 ^ 31.0)
define function longToInteger32(x:Integer) : Integer {
  let shift = maxInteger32 + 1;
  return (x + shift) % (maxPosInteger32 + 1) - shift
}

// Math operations
define function acos(x:Double) : Double
define function asin(x:Double) : Double
define function atan(x:Double) : Double
define function atan2(x:Double, y:Double) : Double
define function cos(x:Double) : Double
define function cosh(x:Double) : Double
define function sin(x:Double) : Double
define function sinh(x:Double) : Double
define function tan(x:Double) : Double
define function tanh(x:Double) : Double

// String operations
define function doubleOpt(x:String) : Double?
define function double(x:String) : Double {
	match doubleOpt(x) with
	let? v then return v
	else return nan
}
define function integerOpt(x:String) : Integer? {
	match doubleOpt(x) with
	let? v then return some(doubleToInteger(v))
	else return none
}
define function integer(x:String) : Integer {
	match integerOpt(x) with
	let? v then return v
	else return 0
}
define function longOpt(x:String) : Long? {
	return integerOpt(x)
}
define function long(x:String) : Long {
	return integer(x)
}
define function length(x:String) : Long
define function join(x:String, y:String[]) : String
define function encode(x:String) : String
define function decode(x:String) : String

// Log operations
define function logString(x:String) : Unit

// Polymorphic operations
define function toText(x:Any) : String
define function toString(x:Any) : String
define function distinct(x:Any[]) : Any[]
define function count(x:Any[]) : Integer
define function flatten(x:Any[][]) : Any[]
define function singleton(x:Any[]) : Any
define function arrayAdd(x:Any[],y:Any[]) : Any[]
define function arraySubtract(x:Any[],y:Any[]) : Any[]
define function inArray(x:Any,y:Any[]) : Boolean
define function containsAll(l1:Any[], l2:Any[]) : Boolean {
	return arraySubtract(l1,l2) = []
}

define transaction ErgoErrorResponse extends ErrorResponse{
	message : String
}
define function failure(x:String) : ErgoErrorResponse {
	return ErgoErrorResponse{
		message: x
	}
}

// Currently set options
define function getOptions() : ~org.accordproject.ergo.options.Options

|xxx}
let etime = {xxx|
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

namespace org.accordproject.time

// DateTime operations
// Current DateTime
define function now() : DateTime
// Parse a DateTime
define function dateTime(x:String) : DateTime

// DateTime components
define function getSecond(x:DateTime) : Long
define function getMinute(x:DateTime) : Long
define function getHour(x:DateTime) : Long
define function getDay(x:DateTime) : Long
define function getWeek(x:DateTime) : Long
define function getMonth(x:DateTime) : Long
define function getQuarter(x:DateTime) : Long
define function getYear(x:DateTime) : Long

// Comparisons between dates
define function isAfter(x:DateTime, y:DateTime) : Boolean
define function isBefore(x:DateTime, y:DateTime) : Boolean
define function isSame(x:DateTime, y:DateTime) : Boolean

// Aggregate functions on dates
define function dateTimeMin(x:DateTime[]) : DateTime
define function dateTimeMax(x:DateTime[]) : DateTime

// Durations
define function durationSeconds(x:Long) : InternalDuration
define function durationMinutes(x:Long) : InternalDuration
define function durationHours(x:Long) : InternalDuration
define function durationDays(x:Long) : InternalDuration
define function durationWeeks(x:Long) : InternalDuration

define function durationToInternalDuration(du:Duration) : InternalDuration {
	match du.unit
	with seconds then return durationSeconds(du.amount)
	with minutes then return durationMinutes(du.amount)
	with hours then return durationHours(du.amount)
	with ~org.accordproject.time.TemporalUnit.days then return durationDays(du.amount)
	with ~org.accordproject.time.TemporalUnit.weeks then return durationWeeks(du.amount)
	else return durationSeconds(du.amount) // Defaults to seconds
}

define function durationAmount(du:InternalDuration) : Long

define function internalDurationToDuration(du:InternalDuration) : Duration {
	return Duration{ unit: seconds, amount: durationAmount(du) }
}

// Cast a duration to a given temporal unit
define function durationAs(du:Duration, u:TemporalUnit) : Duration {
	if u = du.unit
	then return du
	else
	  let amount = 
  	  match u
	    with seconds then
	      match du.unit
	      with minutes then du.amount * 60
	      with hours then du.amount * 60 * 60
	      with ~org.accordproject.time.TemporalUnit.days then du.amount * 60 * 60 * 24
	      with ~org.accordproject.time.TemporalUnit.weeks then du.amount * 60 * 60 * 24 * 7
	      else du.amount // Default to seconds
	    with minutes then
	      match du.unit
	      with seconds then du.amount / 60
	      with hours then du.amount * 60
	      with ~org.accordproject.time.TemporalUnit.days then du.amount * 60 * 24
	      with ~org.accordproject.time.TemporalUnit.weeks then du.amount * 60 * 24 * 7
	      else du.amount * 60 // Default to seconds
	    with hours then
	      match du.unit
	      with seconds then du.amount / 60 / 60
	      with minutes then du.amount * 60
	      with ~org.accordproject.time.TemporalUnit.days then du.amount * 24
	      with ~org.accordproject.time.TemporalUnit.weeks then du.amount * 24 * 7
	      else du.amount * 60 * 60 // Default to seconds
	    with ~org.accordproject.time.TemporalUnit.days then
	      match du.unit
	      with seconds then du.amount / 60 / 60 / 24
	      with minutes then du.amount * 60 / 24
	      with hours then du.amount / 24
	      with ~org.accordproject.time.TemporalUnit.weeks then du.amount * 7
	      else du.amount / 60 / 60 / 24 // Default to seconds
	    with ~org.accordproject.time.TemporalUnit.weeks then
	      match du.unit
	      with seconds then du.amount / 60 / 60 / 24 / 7
	      with minutes then du.amount * 60 / 24 / 7
	      with hours then du.amount / 24 / 7
	      with ~org.accordproject.time.TemporalUnit.days then du.amount / 7
	      else du.amount / 60 / 60 / 24 / 7 // Default to seconds
	    else // Default to seconds
	      match du.unit
	      with minutes then du.amount * 60
	      with hours then du.amount * 60 * 60
	      with ~org.accordproject.time.TemporalUnit.days then du.amount * 60 * 60 * 24
	      with ~org.accordproject.time.TemporalUnit.weeks then du.amount * 60 * 60 * 24 * 7
	      else du.amount // Default to seconds
		;
		return Duration{ unit: u, amount: amount }
}

// Duration difference between two dates
define function diffInternal(x:DateTime, y:DateTime) : InternalDuration
define function diffDurationAs(x:DateTime, y:DateTime, z:TemporalUnit) : Duration {
	return durationAs(internalDurationToDuration(diffInternal(x,y)),z)
}
define function diffDuration(x:DateTime, y:DateTime) : Duration {
	return diffDurationAs(x, y, seconds) // Defaults to seconds
}

// Add and subtract durations
define function addInternal(x:DateTime, y:InternalDuration) : DateTime
define function addDuration(x:DateTime, y:Duration) : DateTime {
	return addInternal(x,durationToInternalDuration(y))
}

define function subtractInternal(x:DateTime, y:InternalDuration) : DateTime
define function subtractDuration(x:DateTime, y:Duration) : DateTime {
	return subtractInternal(x,durationToInternalDuration(y))
}

define function divideDuration(x:Duration, y:Duration) : Double {
	let du1 = durationToInternalDuration(x);
	let du2 = durationToInternalDuration(y);
	return longToDouble(durationAmount(du1)) / longToDouble(durationAmount(du2))
}

// Periods
define function periodDays(x:Long) : InternalPeriod
define function periodWeeks(x:Long) : InternalPeriod
define function periodMonths(x:Long) : InternalPeriod
define function periodQuarters(x:Long) : InternalPeriod
define function periodYears(x:Long) : InternalPeriod

define function periodToInternalPeriod(du:Period) : InternalPeriod {
	match du.unit
	with days then return periodDays(du.amount)
	with weeks then return periodWeeks(du.amount)
	with months then return periodMonths(du.amount)
	with quarters then return periodQuarters(du.amount)
	with years then return periodYears(du.amount)
	else return periodDays(du.amount) // Defaults to days
}

// Period difference between two dates
define function diffAsMonths(x:DateTime, y:DateTime) : Long {
	let year = getYear(x) - getYear(y);
	let month = getMonth(x) - getMonth(y);
	return year * 12 + month
}
define function diffPeriodAs(x:DateTime, y:DateTime, z:PeriodUnit) : Period {
	match z
	with days
	   then let d = diffDurationAs(x,y,~org.accordproject.time.TemporalUnit.days);
	   return Period{ amount: d.amount, unit: days }
	with ~org.accordproject.time.PeriodUnit.weeks
	   then let w = diffDurationAs(x,y,~org.accordproject.time.TemporalUnit.weeks);
	   return Period{ amount: w.amount, unit: weeks }
	with months then let m = diffAsMonths(x,y); return Period{ amount: m, unit: months }
	with quarters then let m = diffAsMonths(x,y);  return Period{ amount: m / 3, unit: quarters }
	with years then let m = diffAsMonths(x,y); return Period{ amount: m / 12, unit: years }
	else
	   let d = diffDurationAs(x,y,~org.accordproject.time.TemporalUnit.days);
	   return Period{ amount: d.amount, unit: days }
}

// Add and subtract periods
define function addInternalPeriod(x:DateTime, y:InternalPeriod) : DateTime
define function addPeriod(x:DateTime, y:Period) : DateTime {
	return addInternalPeriod(x,periodToInternalPeriod(y))
}

define function subtractInternalPeriod(x:DateTime, y:InternalPeriod) : DateTime
define function subtractPeriod(x:DateTime, y:Period) : DateTime {
	return subtractInternalPeriod(x,periodToInternalPeriod(y))
}

// Move the date to the closest start or end of a period
define function startOfDay(x:DateTime) : DateTime
define function startOfWeek(x:DateTime) : DateTime
define function startOfMonth(x:DateTime) : DateTime
define function startOfQuarter(x:DateTime) : DateTime
define function startOfYear(x:DateTime) : DateTime

define function startOf(x:DateTime, y:PeriodUnit) : DateTime {
	match y
	with days then return startOfDay(x)
	with weeks then return startOfWeek(x)
	with months then return startOfMonth(x)
	with quarters then return startOfQuarter(x)
	with years then return startOfYear(x)
	else return startOfDay(x) // Default to days
}

define function endOfDay(x:DateTime) : DateTime
define function endOfWeek(x:DateTime) : DateTime
define function endOfMonth(x:DateTime) : DateTime
define function endOfQuarter(x:DateTime) : DateTime
define function endOfYear(x:DateTime) : DateTime

define function endOf(x:DateTime, y:PeriodUnit) : DateTime {
	match y
	with days then return endOfDay(x)
	with weeks then return endOfWeek(x)
	with months then return endOfMonth(x)
	with quarters then return endOfQuarter(x)
	with years then return endOfYear(x)
	else return endOfDay(x) // Default to days
}

// Format
define function dateTimeFormatInternal(x:String) : InternalFormat
define function formatInternal(x:DateTime,y:InternalFormat) : String
define function format(x:DateTime,y:String) : String {
	return formatInternal(x,dateTimeFormatInternal(y))
}
|xxx}
let template = {xxx|
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

namespace org.accordproject.ergo.template

define function variableTag(variableName:String,text:String) : String {
	if getOptions().wrapVariables
	then return "<variable id=\"" ++ variableName ++ "\" value=\"" ++ encode(text) ++ "\"/>"
	else return text
}

define function variableTagAs(variableName:String,text:String,format:String) : String {
	if getOptions().wrapVariables
	then return "<variable id=\"" ++ variableName ++ "\" value=\"" ++ encode(text) ++ "\" format=\"" ++ encode(format) ++ "\"/>"
	else return text
}

define function ifBlockTag(variableName:String,text:String) : String {
	if getOptions().wrapVariables
	then return "<if id=\"" ++ variableName ++ "\" value=\"" ++ encode(text) ++ "\"/>"
	else return text
}

define function listBlockTag(text:String) : String {
	if getOptions().wrapVariables
	then return "```<list/>" ++ text ++ "\n```"
	else return text
}

define function computedTag(text:String) : String {
	if getOptions().wrapVariables
	then return "<computed value=\"" ++ encode(text) ++ "\"/>"
	else if getOptions().template
	then return "{{" ++ text ++ "}}"
	else return text
}
|xxx}
let ergo_runtime = {xxx|
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

/* JavaScript runtime for core operators */

/* Utilities */
function mustBeArray(obj) {
    if (Array.isArray(obj)) {
        return;
    }
    throw new Error('Expected an array but got: ' + JSON.stringify(obj));
}
function boxNat(v) {
    return { '$nat': v };
}
function unboxNat(v) {
    return v['$nat'];
}
function isNat(v) {
    return Object.prototype.hasOwnProperty.call(v,'$nat');
}
function boxLeft(v) {
    return { '$left' : v };
}
function unboxLeft(v) {
    return v['$left'];
}
function isLeft(v) {
    return Object.prototype.hasOwnProperty.call(v,'$left');
}
function boxRight(v) {
    return { '$right' : v };
}
function unboxRight(v) {
    return v['$right'];
}
function isRight(v) {
    return Object.prototype.hasOwnProperty.call(v,'$right');
}
function sub_brand(b1,b2) {
    var bsub=null;
    var bsup=null;
    for (var i=0; i<inheritance.length; i=i+1) {
        bsub = inheritance[i].sub;
        bsup = inheritance[i].sup;
        if ((b1 === bsub) && (b2 === bsup)) { return true; }
    }
    return false;
}
// from: https://developer.mozilla.org/en-US/docs/Web/JavaScript/Guide/Regular_Expressions?redirectlocale=en-US&redirectslug=JavaScript%2FGuide%2FRegular_Expressions
function escapeRegExp(string){
    return string.replace(/([.*+?^=!:${}()|\[\]\/\\])/g, '\\$1');
}

/* Generic */
function equal(v1, v2) {
    return compare(v1, v2) === 0;
}
function compare(v1, v2) {
    var t1 = typeof v1, t2 = typeof v2;
    if (t1 === 'object' && v1 !== null) {
        if (isNat(v1)) { t1 = 'number'; v1 = unboxNat(v1); }
    };
    if (t2 === 'object' && v2 !== null) {
        if (isNat(v2)) { t2 = 'number'; v2 = unboxNat(v2); }
    };
    if (t1 != t2) {
        return t1 < t2 ? -1 : +1;
    }
    var a1 = {}.toString.apply(v1), a2 = {}.toString.apply(v2);
    if (a1 != a2) {
        return a1 < a2 ? -1 : +1;
    }
    if (a1 === '[object Array]') {
        v1 = v1.slice(); /* Sorting in place leads to inconsistencies, notably as it re-orders the input WM in the middle of processing */
        v2 = v2.slice(); /* So we do the sort/compare on a clone of the original array */
        v1.sort(compare);
        v2.sort(compare);
    }
    if (t1 === 'object') {
        var fields1 = [];
        var fields2 = [];
        for (var f1 in v1) { fields1.push(f1); }
        for (var f2 in v2) { fields2.push(f2); }
        fields1 = fields1.sort(compare);
        fields2 = fields2.sort(compare);
        for (var i = 0; i < fields1.length; i=i+1) {
            if (!(Object.prototype.hasOwnProperty.call(v2,fields1[i]))) {
                return -1;
            }
            var fc = compare(v1[fields1[i]], v2[fields1[i]]);
            if (fc != 0) {
                return fc;
            }
        }
        for (var i = 0; i < fields2.length; i=i+1) {
            if (!(Object.prototype.hasOwnProperty.call(v1,fields2[i]))) {
                return +1;
            }
        }
        return 0;
    }
    if (v1 != v2) {
        return v1 < v2 ? -1 : +1;
    }
    return 0;
}

/* Record */
function recConcat(r1, r2) {
    var result = { };
    for (var key2 in r2) {
        result[key2] = r2[key2];
    }
    for (var key1 in r1) {
        if (!(Object.prototype.hasOwnProperty.call(r2,key1))) {
            result[key1] = r1[key1];
        }
    }
    return result;
}
function recMerge(r1, r2) {
    var result = { };
    for (var key1 in r1) {
        result[key1] = r1[key1];
    }
    for (var key2 in r2) {
        if (Object.prototype.hasOwnProperty.call(r1,key2)) {
            if (!equal(r1[key2], r2[key2])) {
                return [ ];
            }
        } else {
            result[key2] = r2[key2];
        }
    }
    return [ result ];
}
function recRemove(r, f) {
    var result = { };
    for (var key in r) {
        if (key != f) {
            result[key] = r[key];
        }
    }
    return result;
}
function recProject(r1, p2) {
    var result = { };
    for (var key1 in r1) {
        if (!(p2.indexOf(key1) === -1)) {
            result[key1] = r1[key1];
        }
    }
    return result;
}
function recDot(receiver, member) {
    if (typeof receiver === 'object' && Object.prototype.hasOwnProperty.call(receiver,member)) {
        return receiver[member];
    }
    throw new Error('TypeError: recDot called on non-record');
}

/* Sum */
function either(v) {
    if (typeof v === 'object') {
        if (isLeft(v)) {
            return true;
        } else if (isRight(v)) {
            return false;
        } else {
            throw new Error('TypeError: either called on non-sum');
        }
    }
    throw new Error('TypeError: either called on non-sum');
}
function toLeft(v) {
    if (typeof v === 'object' && isLeft(v)) {
        return unboxLeft(v);
    }
    throw new Error('TypeError: toLeft called on non-sum');
}
function toRight(v) {
    if (typeof v === 'object' && isRight(v)) {
        return unboxRight(v);
    }
    throw new Error('TypeError: toRight called on non-sum');
}

/* Brand */ /* XXX TODO! */
function brand(b,v) {
    v['$class'] = b[0];
    return v
}
function unbrand(v) {
    if (typeof v === 'object')
        if (Object.prototype.hasOwnProperty.call(v,'$class') && !(Object.prototype.hasOwnProperty.call(v,'$data'))) {
            return recRemove(v,'$class');
        } else {
            return (Object.prototype.hasOwnProperty.call(v,'$data')) ? v.$data : v;
        }
    throw ('TypeError: unbrand called on non-object' + JSON.stringify(v));
}
function enhanced_cast(brands,v) {
    var type = v.$class;
    if (brands.length != 1) {
        throw 'Can\'t handle multiple brands yet';
    }
    var brand = brands[0];
    if (brand === type || brand === 'Any' || sub_brand(type, brand)) {
        return boxLeft(v);
    }
    return boxRight(null);
}
function cast(brands,v) {
    mustBeArray(brands);
    if (Object.prototype.hasOwnProperty.call(v,'$class') && !(Object.prototype.hasOwnProperty.call(v,'$data'))) {
        return enhanced_cast(brands,v);
    }
    var type = v.$class;
    mustBeArray(type);
    if (brands.length === 1 && brands[0] === 'Any') { /* cast to top of inheritance is built-in */
        return boxLeft(v);
    }
    brands:
    for (var i in brands) {
        var b = brands[i];
        for (var j in type) {
            var t = type[j];
            if (equal(t,b) || sub_brand(t,b)) {
                continue brands;
            }
        }
        /* the brand b does not appear in the type, so the cast fails */
        return boxRight(null);
    }
    /* All brands appear in the type, so the cast succeeds */
    return boxLeft(v);
}

/* Collection */
function distinct(b) {
    var result = [ ];
    for (var i=0; i<b.length; i=i+1) {
        var v = b[i];
        var dup = false;
        for (var j=i+1; j<b.length; j=j+1) {
            if (equal(v,b[j])) { dup = true; break; }
        }
        if (!(dup)) { result.push(v); } else { dup = false; }
    }
    return result;
}
function singleton(v) {
    if (v.length === 1) {
        return boxLeft(v[0]);
    } else {
        return boxRight(null); /* Not a singleton */
    }
}
function flatten(aOuter) {
    var result = [ ];
    for (var iOuter=0, nOuter=aOuter.length; iOuter<nOuter; iOuter = iOuter+1) {
        var aInner = aOuter[iOuter];
        for (var iInner=0, nInner=aInner.length; iInner<nInner; iInner = iInner+1) {
            result.push(aInner[iInner]);
        }
    }
    return result;
}
function union(b1, b2) {
    var result = [ ];
    for (var i1=0; i1<b1.length; i1=i1+1) {
        result.push(b1[i1]);
    }
    for (var i2=0; i2<b2.length; i2=i2+1) {
        result.push(b2[i2]);
    }
    return result;
}
function minus(b1, b2) {
    var result = [ ];
    var v1 = b1.slice();
    var v2 = b2.slice();
    v1.sort(compare);
    v2.sort(compare);
    var i2=0;
    var length2=v2.length;
    var comp=0;
    for (var i1=0; i1<v1.length; i1=i1+1) {
        while ((i2 < length2) && (compare(v1[i1],v2[i2]) === 1)) i2=i2+1;
        if (i2 < length2) {
            if (compare(v1[i1],v2[i2]) === (-1)) { result.push(v1[i1]); } else { i2=i2+1; }
        } else {
            result.push(v1[i1]);
        }
    }
    return result;
}
function min(b1, b2) {
    var result = [ ];
    var v1 = b1.slice();
    var v2 = b2.slice();
    v1.sort(compare);
    v2.sort(compare);
    var i2=0;
    var length2=v2.length;
    var comp=0;
    for (var i1=0; i1<v1.length; i1=i1+1) {
        while ((i2 < length2) && (compare(v1[i1],v2[i2]) === 1)) i2=i2+1;
        if (i2 < length2) {
            if (compare(v1[i1],v2[i2]) === 0) result.push(v1[i1]);
        }
    }
    return result;
}
function max(b1, b2) {
    var result = [ ];
    var v1 = b1.slice();
    var v2 = b2.slice();
    v1.sort(compare);
    v2.sort(compare);
    var i2=0;
    var length2=v2.length;
    var comp=0;
    for (var i1=0; i1<v1.length; i1=i1+1) {
        while ((i2 < length2) && (compare(v1[i1],v2[i2]) === 1)) { result.push(v2[i2]); i2=i2+1; }
        if (i2 < length2) {
            if (compare(v1[i1],v2[i2]) === 0) i2=i2+1;
        }
        result.push(v1[i1]);
    }
    while (i2 < length2) { result.push(v2[i2]); i2=i2+1; }
    return result;
}
function nth(b1, n) {
    var index = n;
    if (isNat(n)){
        index = unboxNat(n);
    }
    if (b1[index]) {
        return boxLeft(b1[index]);
    } else {
        return boxRight(null);
    }
}
function count(v) {
    return boxNat(v.length);
}
function contains(v, b) {
    for (var i=0; i<b.length; i=i+1) {
        if (equal(v, toLeft(b[i]))) {
            return true;
        }
    }
    return false;
}
function compareOfMultipleCriterias(scl) {
    return function(a,b) {
        var current_compare = 0;
        for (var i=0; i<scl.length; i=i+1) {
            var sc = scl[i];
            if (Object.prototype.hasOwnProperty.call(sc,'asc')) { current_compare = compare(recDot(a,sc['asc']), recDot(b,sc['asc'])); }
            else if (Object.prototype.hasOwnProperty.call(sc,'desc')) { current_compare = -(compare(recDot(a,sc['asc']), recDot(b,sc['asc']))); }

            if (current_compare === -1) { return -1; }
            else if (current_compare === 1) { return 1; }
        }
        return current_compare;
    }
    
}
function sort(b,scl) {
    var result = [ ];
    if (scl.length === 0) { return b; } // Check for no sorting criteria
    var compareFun = compareOfMultipleCriterias(scl);
    result = b.slice(); /* Sorting in place leads to inconsistencies, notably as it re-orders the input WM in the middle of processing */
    result.sort(compareFun);
    return result;
}
function groupByOfKey(l,k,keysf) {
    result = [ ];
    l.forEach((x) => {
        if (equal(keysf(x),k)) {
            result.push(x);
        }
    });
    return result;
}
function groupByNested(l,keysf) {
    var keys = distinct(l.map(keysf));
    var result = [ ];
    keys.forEach((k) => {
        result.push({ 'keys': k, 'group' : groupByOfKey(l,k,keysf) });
    });
    return result;
}
function groupBy(g,kl,l) {
    // g is partition name
    // kl is key list
    // l is input collection of records
    var keysf = function (j) {
        return recProject(j,kl);
    };
    var grouped = groupByNested(l,keysf);
    var result = [ ];
    grouped.forEach((x) => {
        var gRec = {};
        gRec[g] = x.group;
        result.push(recConcat(x.keys, gRec));
    });
    return result;
}

/* String */
function length(v) {
    return boxNat(v.length);
}
function substring(v, start, len) {
    return v.substring(unboxNat(start),unboxNat(len));
}
function substringEnd(v, start) {
    return v.substring(unboxNat(start));
}
function stringJoin(sep, v) {
    return v.join(sep);
}
function like(pat, s) {
    var reg1 = escapeRegExp(pat);
    var reg2 = reg1.replace(/_/g, '.').replace(/%/g, '.*');
    var reg3 = new RegExp(reg2);
    return reg3.test(s);
}

/* Integer */
function natLt(v1, v2) {
    return unboxNat(v1) < unboxNat(v2);
}
function natLe(v1, v2) {
    return unboxNat(v1) <= unboxNat(v2);
}
function natPlus(v1, v2) {
    return boxNat(unboxNat(v1) + unboxNat(v2));
}
function natMinus(v1, v2) {
    return boxNat(unboxNat(v1) - unboxNat(v2));
}
function natMult(v1, v2) {
    return boxNat(unboxNat(v1) * unboxNat(v2));
}
function natDiv(v1, v2) {
    return boxNat(Math.floor(unboxNat(v1) / unboxNat(v2)));
}
function natRem(v1, v2) {
    return boxNat(Math.floor(unboxNat(v1) % unboxNat(v2)));
}
function natAbs(v) {
    return boxNat(Math.abs(unboxNat(v1),unboxNat(v2)));
}
function natLog2(v) {
    return boxNat(Math.floor(Math.log2(unboxNat(v)))); // Default Z.log2 is log_inf, biggest integer lower than log2
}
function natSqrt(v) {
    return boxNat(Math.floor(Math.sqrt(unboxNat(v)))); // See Z.sqrt biggest integer lower than sqrt
}
function natMinPair(v1, v2) {
    return boxNat(Math.min(unboxNat(v1),unboxNat(v2)));
}
function natMaxPair(v1, v2) {
    return boxNat(Math.max(unboxNat(v1),unboxNat(v2)));
}
function natSum(b) {
    var result = 0;
    for (var i=0; i<b.length; i=i+1) {
        result += unboxNat(b[i]);
    }
    return boxNat(result);
}
function natMin(b) {
    var numbers = [ ];
    for (var i=0; i<b.length; i=i+1) {
        numbers.push(unboxNat(b[i]));
    }
    return boxNat(Math.min.apply(Math,numbers));
}
function natMax(b) {
    var numbers = [ ];
    for (var i=0; i<b.length; i=i+1) {
        numbers.push(unboxNat(b[i]));
    }
    return boxNat(Math.max.apply(Math,numbers));
}
function natArithMean(b) {
    var len = b.length;
    if (len === 0) {
        return boxNat(0);
    } else {
        return boxNat(Math.floor(natSum(b)/len));
    }
}
function floatOfNat(v) {
    return unboxNat(v);
}

/* Float */
function floatSum(b) {
    var result = 0;
    for (var i=0; i<b.length; i=i+1) {
        result += b[i];
    }
    return result;
}
function floatArithMean(b) {
    var len = b.length;
    if (len === 0) {
        return 0;
    } else {
        return floatSum(b)/len;
    }
}
function natOfFloat(v) {
    return boxNat(Math.trunc(v));
}

/* Unwrapping errors on output */
function unwrapError(result) {
    if (result.hasOwnProperty('$left')) {
        return toLeft(result);
    } else {
        var failure = toRight(result);
        var message = "Unknown Ergo Logic Error (Please file a GitHub issue)";
        if (either(cast(["org.accordproject.ergo.stdlib.ErgoErrorResponse"],failure))) {
            message = unbrand(toLeft(cast(["org.accordproject.ergo.stdlib.ErgoErrorResponse"],failure))).message;
        } else {
            message = JSON.stringify(toRight(cast(["org.accordproject.ergo.stdlib.ErgoErrorResponse"],failure)));
        }
        throw new Error("[Ergo] " + message);
    }
}
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

/* JavaScript runtime for core operators */

function isEnum(v) {
  if (v.$class) {
        return either(cast(["org.accordproject.base.Enum"],v));
    } else {
        return false;
    }
}
function toString(v) {
    return toStringQ(v, "\"");
}
function toText(v) {
    return toTextQ(v, "\"");
}
function toStringQ(v, quote) {
    if (v === null)
        return "null";
    var t = typeof v;
    if (t == "string")
        return quote + v + quote;
    if (t == "boolean")
        return "" + v;
    if (t == "number") {
        if (Math.floor(v) == v) return (new Number(v)).toFixed(1); // Make sure there is always decimal point
        else return "" + v;
    }
    if ({}.toString.apply(v) == "[object Array]") {
        v = v.slice();
        v.sort();
        var result = "[";
        for (var i=0, n=v.length; i<n; i++) {
            if (i > 0)
                result += ", ";
            result += toStringQ(v[i], quote);
        }
        return result + "]";
    }
    if(moment.isMoment(v)) {
        return v.format('MM/DD/YYYY');
    }
    if(v.hasOwnProperty('$nat')){
        return "" + v.$nat;
    }
    if (isEnum(v)) {
        var enumval = v.$data;
        while (!enumval.$left) {
            enumval = enumval.$right;
        }
        return "" + enumval.$left
    }
    var result2 = "{";
    var first = true;
    for (var key in v) {
        if (first) first = false; else result2 += ", ";
        result2 += toStringQ(key, quote) + ": " + toStringQ(v[key], quote);
    }
    result2 += "}";
    return result2;
}
function toTextQ(v, quote) {
    if (v === null)
        return "null";
    var t = typeof v;
    if (t == "string")
        return quote + v + quote;
    if (t == "boolean")
        return "" + v;
    if (t == "number") {
        if (Math.floor(v) == v) return (new Number(v)).toFixed(1); // Make sure there is always decimal point
        else return "" + v;
    }
    if ({}.toString.apply(v) == "[object Array]") {
        v = v.slice();
        v.sort();
        var result = "";
        for (var i=0, n=v.length; i<n; i++) {
            if (i > 0)
                result += "";
          result += toTextQ(v[i], quote);
        }
        return result + "";
    }
    if (moment.isMoment(v)) {
        return v.format('MM/DD/YYYY');
    }
    if(v.hasOwnProperty('$nat')){
        return "" + v.$nat;
    }
    if (isEnum(v)) {
        var enumval = v.$data;
        while (!enumval.$left) {
            enumval = enumval.$right;
        }
        return "" + enumval.$left
    }
    var result2 = "";
    var first = true;
    for (var key in v) {
        if (key !== "$class") {
            if (first) first = false; else result2 += " ";
            result2 += toTextQ(v[key], quote);
        }
    }
    return result2;
}
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

/* JavaScript runtime for DateTime component */

/* Utilities */
var SECONDS = "second";
var MINUTES = "minute";
var HOURS = "hour";
var DAYS = "day";
var WEEKS = "week";
var MONTHS = "month";
var QUARTERS = "quarter";
var YEARS = "year";

function mustBeDate(date) {
    if (typeof date == "string") {
        return moment.parseZone(date).utcOffset(utcOffset, false);
    } else if (date instanceof Date) {
        return moment(date).utcOffset(utcOffset, false);
    } else {
        return date.clone().utcOffset(utcOffset, false);;
    }
}
function mustBeDateArray(dateArray) {
    var newDateArray = [];
    for (var i=0; i<dateArray.length; i++) {
        newDateArray.push(mustBeDate(dateArray[i]));
    }
    return newDateArray;
}
function mustBeDuration(d) {
    if (typeof d == "string") {
        return moment.duration(d);
    } else {
        return d.clone();
    }
}
function mustBeUnit(unit) {
    if (unit === SECONDS
        || unit === MINUTES
        || unit === HOURS
        || unit === DAYS
        || unit === WEEKS
        || unit === MONTHS
        || unit === QUARTERS
        || unit === YEARS)
	      return;
    throw new Error("Expected a duration unit but got " + JSON.stringify(unit));
}

function compareDates(date1, date2) {
    date1 = mustBeDate(date1);
    date2 = mustBeDate(date2);
    if (date1.isBefore(date2)) {
        return -1;
    } else if (date1.isAfter(date2)) {
        return 1;
    } else if (date1.isSame(date2)) {
        return 0;
    }
    throw new Error("Unexpected failure: compareDates")
}

/* DateTime */
function dateTimeGetSeconds(date) {
    date = mustBeDate(date);
    return boxNat(date.second());
}
function dateTimeGetMinutes(date) {
    date = mustBeDate(date);
    return boxNat(date.minute());
}
function dateTimeGetHours(date) {
    date = mustBeDate(date);
    return boxNat(date.hour());
}
function dateTimeGetDays(date) {
    date = mustBeDate(date);
    return boxNat(date.date());
}
function dateTimeGetWeeks(date) {
    date = mustBeDate(date);
    return boxNat(date.week());
}
function dateTimeGetMonths(date) {
    date = mustBeDate(date);
    return boxNat(date.month() + 1);
}
function dateTimeGetQuarters(date) {
    date = mustBeDate(date);
    return boxNat(date.quarter());
}
function dateTimeGetYears(date) {
    date = mustBeDate(date);
    return boxNat(date.year());
}

function dateTimeStartOfDay(date) {
    date = mustBeDate(date);
    return date.startOf('day');
}
function dateTimeStartOfWeek(date) {
    date = mustBeDate(date);
    return date.startOf('week');
}
function dateTimeStartOfMonth(date) {
    date = mustBeDate(date);
    return date.startOf('month');
}
function dateTimeStartOfQuarter(date) {
    date = mustBeDate(date);
    return date.startOf('quarter');
}
function dateTimeStartOfYear(date) {
    date = mustBeDate(date);
    return date.startOf('year');
}

function dateTimeEndOfDay(date) {
    date = mustBeDate(date);
    return date.endOf('day');
}
function dateTimeEndOfWeek(date) {
    date = mustBeDate(date);
    return date.endOf('week');
}
function dateTimeEndOfMonth(date) {
    date = mustBeDate(date);
    return date.endOf('month');
}
function dateTimeEndOfQuarter(date) {
    date = mustBeDate(date);
    return date.endOf('quarter');
}
function dateTimeEndOfYear(date) {
    date = mustBeDate(date);
    return date.endOf('year');
}
/* DateTime Formating */
function dateTimeFormatFromString(s) {
  return s;
}
function dateTimeFromString(stringDate) {
    return moment.parseZone(stringDate).utcOffset(utcOffset, false);
}

var minDateTime = moment.parseZone("0001-01-01 00:00:00").utcOffset(utcOffset, false);
var maxDateTime = moment.parseZone("3268-01-21 23:59:59").utcOffset(utcOffset, false);
function dateTimeMax(v) {
    var v1 = mustBeDateArray(v);
    if (v1.length === 0) {
        return minDateTime;
    } else {
        return moment.max(v1);
    }
}
function dateTimeMin(v) {
    var v1 = mustBeDateArray(v);
    if (v1.length === 0) {
        return maxDateTime;
    } else {
        return moment.min(v1);
    }
}

function dateTimeDurationAmount(v) {
    v = mustBeDuration(v);
    return boxNat(v.asSeconds());
}

function dateTimeDurationFromString(stringDuration) {
    // TODO verify what the string format for durations is going to be.
    // Here we assume a number adjoined to a valid unit with a dash.
    if (typeof stringDuration === "string") {
	      var parts = stringDuration.split("-");
	      if (parts.length === 2) {
	          mustBeUnit(parts[1]);
            return moment.duration(parseFloat(parts[0]),parts[1]+"s");
        }
    }
    throw new Error("Not well formed duration input: " + stringDuration);
}

function dateTimeDurationFromSeconds(v) {
    var num = unboxNat(v);
    return moment.duration(num,'second');
}
function dateTimeDurationFromMinutes(v) {
    var num = unboxNat(v);
    return moment.duration(num,'minute');
}
function dateTimeDurationFromHours(v) {
    var num = unboxNat(v);
    return moment.duration(num,'hour');
}
function dateTimeDurationFromDays(v) {
    var num = unboxNat(v);
    return moment.duration(num,'day');
}
function dateTimeDurationFromWeeks(v) {
    var num = unboxNat(v);
    return moment.duration(num,'week');
}

function dateTimePeriodFromString(stringDuration) {
    return dateTimeDurationFromString(stringDuration);
}
function dateTimePeriodFromDays(v) {
    var num = unboxNat(v);
    return moment.duration(num,'day');
}
function dateTimePeriodFromWeeks(v) {
    var num = unboxNat(v);
    return moment.duration(num,'week');
}
function dateTimePeriodFromMonths(v) {
    var num = unboxNat(v);
    return moment.duration(num,'month');
}
function dateTimePeriodFromQuarters(v) {
    var num = unboxNat(v);
    return moment.duration(num * 3,'month');
}
function dateTimePeriodFromYears(v) {
    var num = unboxNat(v);
    return moment.duration(num,'year');
}

function dateTimeFormat(date,f) {
  date = mustBeDate(date);
  return date.format(f);
}

function dateTimeAdd(date, duration) {
    date = mustBeDate(date);
    duration = mustBeDuration(duration);
    return date.add(duration);
}
function dateTimeSubtract(date, d) {
    date = mustBeDate(date);
    d = mustBeDuration(d);
    return date.subtract(d);
}

function dateTimeAddPeriod(date, period) {
    date = mustBeDate(date);
    period = mustBeDuration(period);
    return date.add(period);
}
function dateTimeSubtractPeriod(date, period) {
    date = mustBeDate(date);
    period = mustBeDuration(period);
    return date.subtract(period);
}

function dateTimeIsSame(date1, date2) {
    return compareDates(date1, date2) === 0;
}
function dateTimeIsBefore(date1, date2) {
    return compareDates(date1,date2) < 0;
}
function dateTimeIsAfter(date1, date2) {
    return compareDates(date1, date2) > 0;
}

function dateTimeDiff(date1, date2) {
    date1 = mustBeDate(date1);
    date2 = mustBeDate(date2);
    return moment.duration(date1.diff(date2,'seconds'),'seconds');
}

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

/* JavaScript runtime for Uri component */

function uriEncode(v) {
  return encodeURIComponent(v);
}

function uriDecode(v) {
  return decodeURIComponent(v);
}
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

/* Addendum to the Ergo runtime for the math library */

function floatOfString(s) {
    // Check whether we're dealing with nan, since it's the error case for Number.parseFloat
    if (s === 'nan') {
        return NaN;
    } else {
        let num = Number.parseFloat(s);
        if (Number.isNaN(num)) {
            return null;
        } else {
            return num
        }
    }
}
function acos(x) { return Math.acos(x); }
function asin(x) { return Math.asin(x); }
function atan(x) { return Math.atan(x); }
function atan2(y, x) { return Math.atan2(y, x); }
function cos(x) { return Math.cos(x); }
function cosh(x) { return Math.cosh(x); }
function sin(x) { return Math.sin(x); }
function sinh(x) { return Math.sinh(x); }
function tan(x) { return Math.tan(x); }
function tanh(x) { return Math.tanh(x); }

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

/* Addendum to the Ergo runtime for Loggingsupport */

/* Logging */
function logString(v) {
  logger.info(v);
}

|xxx}
let builddate = {xxx|Feb 18, 2020|xxx}
