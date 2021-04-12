let runtime = {runtime|
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
/* XXX TODO
   -- never use 'in' always use 'hasObjectProperty()' instead
   -- never use '==' or '!=' always use '===' or '!==' instead
   -- never use 'i++' always use 'i = i+1'
*/

/* Utilities */
function mustBeArray(obj) {
    if (Array.isArray(obj)) {
        return;
    }
    throw new Error("Expected an array but got: " + JSON.stringify(obj));
}
function natBox(v) {
    return { "$nat": v };
}
function natUnbox(v) {
    return v.$nat;
}
function mkLeft(v) {
    return { "$left" : v };
}
function mkRight(v) {
    return { "$right" : v };
}
function sub_brand(b1,b2) {
    var bsub=null;
    var bsup=null;
    for (var i=0; i<inheritance.length; i++) {
        bsub = inheritance[i].sub;
        bsup = inheritance[i].sup;
        if ((b1 == bsub) && (b2 == bsup)) return true;
    }
    return false;
}
function isEnum(v) {
  if (v.type) {
        var isE = either(cast(["org.accordproject.base.Enum"],v));
        return isE;
    } else {
        return false;
    }
}
// from: https://developer.mozilla.org/en-US/docs/Web/JavaScript/Guide/Regular_Expressions?redirectlocale=en-US&redirectslug=JavaScript%2FGuide%2FRegular_Expressions
function escapeRegExp(string){
    return string.replace(/([.*+?^=!:${}()|\[\]\/\\])/g, "\\$1");
}

/* Generic */
function equal(v1, v2) {
    return compare(v1, v2) == 0;
}
function compare(v1, v2) {
    var t1 = typeof v1, t2 = typeof v2;
    if (t1 == "object" && v1 !== null) {
        if (v1.hasOwnProperty('$nat')) { t1 = "number"; v1 = v1.$nat; }
    };
    if (t2 == "object" && v2 !== null) {
        if (v2.hasOwnProperty('$nat')) { t2 = "number"; v2 = v2.$nat; }
    };
    if (t1 != t2)
        return t1 < t2 ? -1 : +1;
    var a1 = {}.toString.apply(v1), a2 = {}.toString.apply(v2);
    if (a1 != a2)
        return a1 < a2 ? -1 : +1;
    if (a1 == "[object Array]") {
        v1 = v1.slice(); /* Sorting in place leads to inconsistencies, notably as it re-orders the input WM in the middle of processing */
        v2 = v2.slice(); /* So we do the sort/compare on a clone of the original array */
        v1.sort(compare);
        v2.sort(compare);
    }
    if (t1 == "object") {
        var fields1 = [];
        var fields2 = [];
        for (var f1 in v1) { fields1.push(f1); }
        for (var f2 in v2) { fields2.push(f2); }
        fields1 = fields1.sort(compare);
        fields2 = fields2.sort(compare);
        for (var i = 0; i < fields1.length; i++) {
            if (!(fields1[i] in v2))
                return -1;
            var fc = compare(v1[fields1[i]], v2[fields1[i]]);
            if (fc != 0)
                return fc;
        }
        for (var i = 0; i < fields2.length; i++) {
            if (!(fields2[i] in v1))
                return +1;
        }
        return 0;
    }
    if (v1 != v2)
        return v1 < v2 ? -1 : +1;
    return 0;
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
        var enumval = v.data;
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
        var enumval = v.data;
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

/* Record */
function recConcat(r1, r2) {
    var result = { };
    for (var key2 in r2)
        result[key2] = r2[key2];
    for (var key1 in r1)
        if (!(key1 in r2))
            result[key1] = r1[key1];
    return result;
}
function recMerge(r1, r2) {
    var result = { };
    for (var key1 in r1)
        result[key1] = r1[key1];
    for (var key2 in r2) {
        if (key2 in r1) {
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
    for (var key in r)
        if (key != f)
            result[key] = r[key];
    return result;
}
function recProject(r1, p2) {
    var result = { };
    for (var key1 in r1) {
        if (!(p2.indexOf(key1) == -1))
            result[key1] = r1[key1];
    }
    return result;
}
function recDot(receiver, member) {
    if (typeof receiver === "object" && member in receiver) {
        return receiver[member];
    }
    throw new Error("TypeError: recDot called on non-record");
}

/* Sum */
function either(v) {
    if (typeof v === "object") {
        if ("$left" in v) {
            return true;
        } else if ("$right" in v) {
            return false;
        } else {
            throw new Error("TypeError: either called on non-sum");
        }
    }
    throw new Error("TypeError: either called on non-sum");
}
function toLeft(v) {
    if (typeof v === "object" && "$left" in v) {
        return v.$left;
    }
    throw new Error("TypeError: toLeft called on non-sum");
}
function toRight(v) {
    if (typeof v === "object" && "$right" in v) {
        return v.$right;
    }
    throw new Error("TypeError: toRight called on non-sum");
}

/* Brand */ /* XXX TODO! */
function brand(b,v) {
    v['$class'] = b[0];
    return v
}
function unbrand(v) {
    if (typeof v === "object")
        if ("$class" in v) {
            return recRemove(v,"$class");
        } else {
            return ("data" in v) ? v.data : v;
        }
    throw ("TypeError: unbrand called on non-object" + JSON.stringify(v));
}
function enhanced_cast(brands,v) {
    var type = v.$class;
    if (brands.length != 1)
        throw "Can't handle multiple brands yet";
    var brand = brands[0];
    if (brand == type || brand == "Any" || sub_brand(type, brand)) {
        return mkLeft(v);
    }
    return mkRight(null);
}
function cast(brands,v) {
    mustBeArray(brands);
    if ("$class" in v)
        return enhanced_cast(brands,v);
    var type = v.type;
    mustBeArray(type);
    if (brands.length == 1 && brands[0] == "Any") { /* cast to top of inheritance is built-in */
        return mkLeft(v);
    }
    brands:
    for (var i in brands) {
        var b = brands[i];
        for (var j in type) {
            var t = type[j];
            if (equal(t,b) || sub_brand(t,b))
                continue brands;
        }
        /* the brand b does not appear in the type, so the cast fails */
        return mkRight(null);
    }
    /* All brands appear in the type, so the cast succeeds */
    return mkLeft(v);
}

/* Collection */
function distinct(b) {
    var result = [ ];
    for (var i=0; i<b.length; i++) {
        var v = b[i];
        var dup = false;
        for (var j=0; j<result.length;j++) {
            if (equal(v,result[j])) { dup = true; break; }
        }
        if (!(dup)) { result.push(v); } else { dup = false; }
    }
    return result;
}
function singleton(v) {
    if (v.length == 1) {
        return mkLeft(v[0]);
    } else {
        return mkRight(null); /* Not a singleton */
    }
}
function flatten(aOuter) {
    var result = [ ];
    for (var iOuter=0, nOuter=aOuter.length; iOuter<nOuter; iOuter++) {
        var aInner = aOuter[iOuter];
        for (var iInner=0, nInner=aInner.length; iInner<nInner; iInner++)
            result.push(aInner[iInner]);
    }
    return result;
}
function union(b1, b2) {
    var result = [ ];
    for (var i1=0; i1<b1.length; i1++)
        result.push(b1[i1]);
    for (var i2=0; i2<b2.length; i2++)
        result.push(b2[i2]);
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
    for (var i1=0; i1<v1.length; i1++) {
        while ((i2 < length2) && (compare(v1[i1],v2[i2]) == 1)) i2++;
        if (i2 < length2) {
            if(compare(v1[i1],v2[i2]) == (-1)) { result.push(v1[i1]); } else { i2++; }
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
    for (var i1=0; i1<v1.length; i1++) {
        while ((i2 < length2) && (compare(v1[i1],v2[i2]) == 1)) i2++;
        if (i2 < length2) {
            if(compare(v1[i1],v2[i2]) == 0) result.push(v1[i1]);
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
    for (var i1=0; i1<v1.length; i1++) {
        while ((i2 < length2) && (compare(v1[i1],v2[i2]) == 1)) { result.push(v2[i2]); i2++; }
        if (i2 < length2) {
            if(compare(v1[i1],v2[i2]) == 0) i2++;
        }
        result.push(v1[i1]);
    }
    while (i2 < length2) { result.push(v2[i2]); i2++; }
    return result;
}
function nth(b1, n) {
    var index = n;
    if(n.hasOwnProperty('$nat')){
        index = n.$nat;
    }
    if (b1[index]) {
        return mkLeft(b1[index]);
    } else {
        return mkRight(null);
    }
}
function count(v) {
    return natBox(v.length);
}
function contains(v, b) {
    for (var i=0; i<b.length; i++)
        if (equal(v, toLeft(b[i])))
            return true;
    return false;
}
function compareOfMultipleCriterias(scl) {
    return function(a,b) {
        var current_compare = 0;
        for (var i=0; i<scl.length; i++) {
            var sc = scl[i];
            if ("asc" in sc) { current_compare = compare(recDot(a,sc['asc']), recDot(b,sc['asc'])); }
            else if ("desc" in sc) { current_compare = -(compare(recDot(a,sc['asc']), recDot(b,sc['asc']))); }

            if (current_compare == -1) { return -1; }
            else if(current_compare == 1) { return 1; }
        }
        return current_compare;
    }
    
}
function sort(b,scl) {
    var result = [ ];
    if (scl.length == 0) { return b; } // Check for no sorting criteria
    var compareFun = compareOfMultipleCriterias(scl);
    result = b.slice(); /* Sorting in place leads to inconsistencies, notably as it re-orders the input WM in the middle of processing */
    result.sort(compareFun);
    return result;
}
function groupBy(l) { // Not implemented
    throw new Error("groupBy not implemented");
}

/* String */
function length(v) {
    return natBox(v.length);
}
function substring(v, start, len) {
    return v.substring(natUnbox(start),natUnbox(len));
}
function substringEnd(v, start) {
    return v.substring(natUnbox(start));
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
    return natUnbox(v1) < natUnbox(v2);
}
function natLe(v1, v2) {
    return natUnbox(v1) <= natUnbox(v2);
}
function natPlus(v1, v2) {
    return natBox(natUnbox(v1) + natUnbox(v2));
}
function natMinus(v1, v2) {
    return natBox(natUnbox(v1) - natUnbox(v2));
}
function natMult(v1, v2) {
    return natBox(natUnbox(v1) * natUnbox(v2));
}
function natDiv(v1, v2) {
    return natBox(Math.floor(natUnbox(v1) / natUnbox(v2)));
}
function natRem(v1, v2) {
    return natBox(Math.floor(natUnbox(v1) % natUnbox(v2)));
}
function natAbs(v) {
    return natBox(Math.abs(natUnbox(v1),natUnbox(v2)));
}
function natLog2(v) {
    return natBox(Math.floor(Math.log2(natUnbox(v)))); // Default Z.log2 is log_inf, biggest integer lower than log2
}
function natSqrt(v) {
    return natBox(Math.floor(Math.sqrt(natUnbox(v)))); // See Z.sqrt biggest integer lower than sqrt
}
function natMinPair(v1, v2) {
    return natBox(Math.min(natUnbox(v1),natUnbox(v2)));
}
function natMaxPair(v1, v2) {
    return natBox(Math.max(natUnbox(v1),natUnbox(v2)));
}
function natSum(b) {
    var result = 0;
    for (var i=0; i<b.length; i++)
        result += natUnbox(b[i]);
    return natBox(result);
}
function natMin(b) {
    var numbers = [ ];
    for (var i=0; i<b.length; i++)
        numbers.push(natUnbox(b[i]));
    return natBox(Math.min.apply(Math,numbers));
}
function natMax(b) {
    var numbers = [ ];
    for (var i=0; i<b.length; i++)
        numbers.push(natUnbox(b[i]));
    return natBox(Math.max.apply(Math,numbers));
}
function natArithMean(b) {
    var len = b.length;
    if(len == 0) {
        return natBox(0);
    } else {
        return natBox(Math.floor(natSum(b)/len));
    }
}
function floatOfNat(v) {
    return natUnbox(v);
}

/* Float */
function floatSum(b) {
    var result = 0;
    for (var i=0; i<b.length; i++)
        result += b[i];
    return result;
}
function floatArithMean(b) {
    var len = b.length;
    if(len == 0) {
        return 0;
    } else {
        return floatSum(b)/len;
    }
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
    return natBox(date.second());
}
function dateTimeGetMinutes(date) {
    date = mustBeDate(date);
    return natBox(date.minute());
}
function dateTimeGetHours(date) {
    date = mustBeDate(date);
    return natBox(date.hour());
}
function dateTimeGetDays(date) {
    date = mustBeDate(date);
    return natBox(date.date());
}
function dateTimeGetWeeks(date) {
    date = mustBeDate(date);
    return natBox(date.week());
}
function dateTimeGetMonths(date) {
    date = mustBeDate(date);
    return natBox(date.month() + 1);
}
function dateTimeGetQuarters(date) {
    date = mustBeDate(date);
    return natBox(date.quarter());
}
function dateTimeGetYears(date) {
    date = mustBeDate(date);
    return natBox(date.year());
}

function dateTimeStartOfDay(date) {
    date = mustBeDate(date);
    mustBeUnit(part);
    return date.startOf('day');
}
function dateTimeStartOfWeek(date) {
    date = mustBeDate(date);
    mustBeUnit(part);
    return date.startOf('week');
}
function dateTimeStartOfMonth(date) {
    date = mustBeDate(date);
    mustBeUnit(part);
    return date.startOf('month');
}
function dateTimeStartOfQuarter(date) {
    date = mustBeDate(date);
    mustBeUnit(part);
    return date.startOf('quarter');
}
function dateTimeStartOfYear(date) {
    date = mustBeDate(date);
    mustBeUnit(part);
    return date.startOf('year');
}

function dateTimeEndOfDay(date) {
    date = mustBeDate(date);
    mustBeUnit(part);
    return date.endOf('day');
}
function dateTimeEndOfWeek(date) {
    date = mustBeDate(date);
    mustBeUnit(part);
    return date.endOf('week');
}
function dateTimeEndOfMonth(date) {
    date = mustBeDate(date);
    mustBeUnit(part);
    return date.endOf('month');
}
function dateTimeEndOfQuarter(date) {
    date = mustBeDate(date);
    mustBeUnit(part);
    return date.endOf('quarter');
}
function dateTimeEndOfYear(date) {
    date = mustBeDate(date);
    mustBeUnit(part);
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
    return natBox(v.asSeconds());
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
    var num = natUnbox(v);
    return moment.duration(num,'second');
}
function dateTimeDurationFromMinutes(v) {
    var num = natUnbox(v);
    return moment.duration(num,'minute');
}
function dateTimeDurationFromHours(v) {
    var num = natUnbox(v);
    return moment.duration(num,'hour');
}
function dateTimeDurationFromDays(v) {
    var num = natUnbox(v);
    return moment.duration(num,'day');
}
function dateTimeDurationFromWeeks(v) {
    var num = natUnbox(v);
    return moment.duration(num,'week');
}

function dateTimePeriodFromString(stringDuration) {
    return dateTimeDurationFromString(stringDuration);
}
function dateTimePeriodFromDays(v) {
    var num = natUnbox(v);
    return moment.duration(num,'day');
}
function dateTimePeriodFromWeeks(v) {
    var num = natUnbox(v);
    return moment.duration(num,'week');
}
function dateTimePeriodFromMonths(v) {
    var num = natUnbox(v);
    return moment.duration(num,'month');
}
function dateTimePeriodFromQuarters(v) {
    var num = natUnbox(v);
    return moment.duration(num * 3,'month');
}
function dateTimePeriodFromYears(v) {
    var num = natUnbox(v);
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

|runtime}
