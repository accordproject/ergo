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

/* "standard library" (implementation of unary and binary operators) */
function unwrap(doc) {
    // Unwrap for Enhanced TxStore format
    if ("state" in doc && !("$class" in doc)) {
	if (doc.state == "COMMITTED")
	    return JSON.parse(doc.currentValue);
	else
	    return null; // Not sure if we will need something more fancy for un-committed data
    }
    // Leave as-is
    else
	return doc;
}
function concat(r1, r2) {
    var result = { };
    for (var key1 in r1)
	result[key1] = r1[key1];
    for (var key2 in r2)
	if (!(key2 in r1))
	    result[key2] = r2[key2];
    return result;
}
function contains(v, b) {
    for (var i=0; i<b.length; i++)
	if (equal(v, toLeft(b[i])))
	    return true;
    return false;
}
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
function fastdistinct(b) {
    b1 = b.slice(); /* Sorting in place leads to inconsistencies, notably as it re-orders the input WM in the middle of processing */
    b1.sort(compare);
    var result = [ ];
    var v1 = null;
    var v2 = null;
    for (var i=0; i<b1.length; i++) {
        var v1 = b1[i];
	if (i == (b1.length -1)) {
	    result.push(v1);
	}
	else {
	    v2 = b1[i+1];
	    if (equal(v1,v2)) {
	    } else {
		result.push(v1);
	    }
	    v1 = v2;
	}
    }
    return result;
}
function compare(v1, v2) {
    var t1 = typeof v1, t2 = typeof v2;
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
function equal(v1, v2) {
    return compare(v1, v2) == 0;
}
function compareOfMultipleCriterias(scl) {
    return function(a,b) {
	var current_compare = 0;
	for (var i=0; i<scl.length; i++) {
	    var sc = scl[i];
	    if ("asc" in sc) { current_compare = compare(deref(a,sc['asc']), deref(b,sc['asc'])); }
	    else if ("desc" in sc) { current_compare = -(compare(deref(a,sc['asc']), deref(b,sc['asc']))); }

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
function flatten(aOuter) {
    var result = [ ];
    for (var iOuter=0, nOuter=aOuter.length; iOuter<nOuter; iOuter++) {
	var aInner = aOuter[iOuter];
	for (var iInner=0, nInner=aInner.length; iInner<nInner; iInner++)
	    result.push(aInner[iInner]);
    }
    return result;
}
function mergeConcat(r1, r2) {
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
function project(r1, p2) {
    var result = { };
    for (var key1 in r1) {
	if (!(p2.indexOf(key1) == -1))
            result[key1] = r1[key1];
    }
    return result;
}
function remove(r, f) {
    var result = { };
    for (var key in r)
	if (key != f)
	    result[key] = r[key];
    return result;
}
function sum(b) {
    var result = 0;
    for (var i=0; i<b.length; i++)
	result += b[i];
    return result;
}

function arithMean(b) {
    var len = b.length;
    if(len == 0) {
	return 0;
    } else {
	return sum(b)/len;
    }
}

function toString(v) {
    return toStringQ(v, "");
}
function toStringQ(v, quote) {
    if (v === null)
	return "null";
    var t = typeof v;
    if (t == "string")
	return quote + v + quote;
    if (t == "number" || t == "boolean")
	return "" + v;
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
    var fs = Object.keys(v);
    var result2 = "{";
    var first = true;
    for (var key in v) {
	if (first) first = false; else result2 += ", ";
	result2 += toStringQ(key, quote) + ": " + toStringQ(v[key], quote);
    }
    return result2 + "}";
}
function bunion(b1, b2) {
    var result = [ ];
    for (var i1=0; i1<b1.length; i1++)
	result.push(b1[i1]);
    for (var i2=0; i2<b2.length; i2++)
	result.push(b2[i2]);
    return result;
}
function bminus(b1, b2) {
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
function bmin(b1, b2) {
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
function bmax(b1, b2) {
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
function sub_brand(b1,b2) {
    var bsub=null;
    var bsup=null;
    var inh = []
    if (inheritance) { inh = inheritance; };
    for (var i=0; i<inh.length; i++) {
	bsub = inh[i].sub;
	bsup = inh[i].sup;
	if ((b1 == bsub) && (b2 == bsup)) return true;
    }
    return false;
}
function left(v) {
    return { left : v };
}
function right(v) {
    return { right : v };
}
function mustBeArray(obj) {
    if (Array.isArray(obj))
	return;
    var e = new Error("Expected an array but got: " + JSON.stringify(obj));
    throw e;
}
function cast(brands,v) {
    mustBeArray(brands);
    if ("$class" in v)
	return enhanced_cast(brands,v);
    var type = v.type;
    mustBeArray(type);
    if (brands.length == 1 && brands[0] == "Any") { /* cast to top of hierarchy is built-in */
    	return left(v);
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
    	return right(null);
    }
    /* All brands appear in the type, so the cast succeeds */
    return left(v);
}
function enhanced_cast(brands,v) {
    var type = v.$class;
    if (brands.length != 1)
	throw "Can't handle multiple brands yet";
    var brand = brands[0];
    if (brand == type || brand == "Any" || sub_brand(type, brand)) {
    	return left(v);
    }
    return right(null);
}
function singleton(v) {
    if (v.length == 1) {
	return left(v[0]);
    } else {
	return right(null); /* Not a singleton */
    }
}
function unbrand(v) {
    if (typeof v === "object")
	if ("$class" in v) {
	    return remove(v,"$class");
	} else {
	    return ("data" in v) ? v.data : v;
	}
    throw "TypeError: unbrand called on non-object";
}
function brand(b,v) {
    v['$class'] = b[0];
    return v
}
function either(v) {
    if (v == null)
	return false;
    if (typeof v === "object")
	return !("right" in v);
    return true;
}
function toLeft(v) {
    if (typeof v === "object") {
	if ("left" in v)
	    return v.left;
	if ("$value" in v)
	    return v.$value;
	if (looksLikeRelationship(v))
	    return v["key"];
    }
    return v;
}
function toRight(v) {
    if (v === null)
	return null;
    if (typeof v === "object" && "right" in v)
	return v.right;
    return undefined;
}
function deref(receiver, member) {
    if (typeof receiver === "object" && member in receiver) {
	var ans = receiver[member];
	if (ans === null) {
	    return null;
	}
	if (typeof ans === "object" && looksLikeRelationship(ans))
	    ans = left(ans["key"]);
	if (("$class" in receiver) && typeof ans === "object" && !("left" in ans) && !Array.isArray(ans))
	    ans = left(ans);
	return ans;
    }
    return undefined;
}
function looksLikeRelationship(v) {
    // As the name suggests, this is only heuristic.  We call it a relationship if it has two or three members.
    // A "key" and "type" member must be among those.   A third member, if present, must be $class and must denote
    // the relationship class.
    var hasKey = false;
    var hasType = false;
    for (var member in v)
	if (member == "key")
	    hasKey = true;
    else if (member == "type")
	hasType = true;
    else if (member == "$class" && v["$class"] == "com.ibm.ia.model.Relationship")
	continue;
    else
	return false;
    return hasKey && hasType;
}
function mkWorld(v) {
    return { "WORLD" : v };
}

// from: https://developer.mozilla.org/en-US/docs/Web/JavaScript/Guide/Regular_Expressions?redirectlocale=en-US&redirectslug=JavaScript%2FGuide%2FRegular_Expressions
function escapeRegExp(string){
    return string.replace(/([.*+?^=!:${}()|\[\]\/\\])/g, "\\$1");
}

/* Addendum to "standard library" with limited support for SQL-style dates and durations (aka "intervals") */

var DAY = "DAY";
var MONTH = "MONTH";
var YEAR = "YEAR";

function sqlGetDateComponent(part, date) {
    date = mustBeDate(date);
    switch(part) {
    case DAY:
	return date.day;
    case MONTH:
	return date.month;
    case YEAR:
	return date.year;
    default:
	throw new Error("Uninterpretable part: " + part);
    }
}

function sqlDateFromString(stringDate) {
    if (typeof stringDate === "string") {
	parts = stringDate.split("-");
	if (parts.length === 3)
	    return makeDate(Number(parts[0]), Number(parts[1]), Number(parts[2]));
	throw new Error("Malformed string date: " + stringDate);
    }
    throw new Error("Expected a date in string form but got " + JSON.stringify(stringDate));
}

function sqlDateDurationFromString(stringDuration) {
    // TODO verify what the string format for durations is going to be.
    // Here we assume a number adjoined to a valid unit with a dash.
    if (typeof stringDuration === "string") {
	parts = stringDuration.split("-");
	if (parts.length === 2) {
	    mustBeUnit(parts[1]);
	    return {"duration": Number(parts[0]), "unit": parts[1]};
	    throw new Error("Malformed string duration: " + stringDuration);
	}
	throw new Error("Expected a duration in string form but got " + JSON.stringify(stringDuration));
    }
}

function sqlDatePointPlus(date, duration) {
    date = mustBeDate(date);
    mustBeDuration(duration);
    switch(duration.unit) {
    case DAY:
	return dateNewDay(date, date.day + duration.duration);
    case MONTH:
	return dateNewMonth(date, date.month + duration.duration);
    case YEAR:
	return dateNewYear(date, date.year + duration.duration);
    default:
	throw new Error("Unexpected state (not supposed to happen)");
    }
}

function sqlDatePointMinus(date, duration) {
    date = mustBeDate(date);
    mustBeDuration(duration);
    switch(duration.unit) {
    case DAY:
	return dateNewDay(date, date.day - duration.duration);
    case MONTH:
	return dateNewMonth(date, date.month - duration.duration);
    case YEAR:
	return dateNewYear(date, date.year - duration.duration);
    default:
	throw new Error("Unexpected bad unit (not supposed to happen)");
    }
}

function sqlDatePointNe(date1, date2) {
    date1 = mustBeDate(date1);
    date2 = mustBeDate(date2);
    return compareDates(date1, date2) != 0;
}

function sqlDatePointLt(date1, date2) {
    date1 = mustBeDate(date1);
    date2 = mustBeDate(date2);
    return date1.isBefore(date2);
}

function sqlDatePointLe(date1, date2) {
    date1 = mustBeDate(date1);
    date2 = mustBeDate(date2);
    return compareDates(date1, date2) <= 0;
}

function sqlDatePointGt(date1, date2) {
    date1 = mustBeDate(date1);
    date2 = mustBeDate(date2);
    return compareDates(date1, date2) > 0;
}

function sqlDatePointGe(date1, date2) {
    date1 = mustBeDate(date1);
    date2 = mustBeDate(date2);
    return compareDates(date1, date2) >= 0;
}

function sqlDateDurationBetween(date1, date2) {
    date1 = mustBeDate(date1);
    date2 = mustBeDate(date2);
    return date1.diff(date2,'days');
}

function compareDates(date1, date2) {
    if (date1.year < date2.year)
	return -1;
    if (date1.year > date2.year)
	return 1;
    if (date1.month < date2.month)
	return -1;
    if (date1.month > date2.month)
	return 1;
    if (date1.day < date2.day)
	return -1;
    if (date1.day > date2.day)
	return 1;
    return 0;
}

function dateNewYear(date, year) {
    return makeDate(year, date.month, date.day);
}

function dateNewMonth(date, month) {
    /* Use Javascript Date object to normalize out-of-range month */
    var jsDate = new Date(date.year, month-1, date.day);
    return makeDate(jsDate.getFullYear(), jsDate.getMonth()+1, jsDate.getDate());
}

function dateNewDay(date, day) {
    /* Use Javascript Date object to normalize out-of-range day */
    var jsDate = new Date(date.year, date.month-1, day);
    return makeDate(jsDate.getFullYear(), jsDate.getMonth()+1, jsDate.getDate());
}

function makeDate(year, month, day) {
    return {"year": year, "month": month, "day": day};
}

function mustBeDate(date) {
    if (typeof date == "string") {
     	return moment(date);
    } else {
	return date;
//     	if (typeof date === "object" && "year" in date && "month" in date && "day" in date)
//     	    return;
//     	throw new Error("Expected a date but got " + JSON.stringify(date));
    }
}

function mustBeDuration(duration) {
    if (typeof duration === "object" && "duration" in duration && "unit" in duration) {
	mustBeUnit(duration.unit);
	return;
    }
    throw new Error("Expected a duration but got " + JSON.stringify(duration));
}

function mustBeUnit(unit) {
    if (unit === DAY || unit === MONTH || unit === YEAR)
	return;
    throw new Error("Expected a duration unit but got " + JSON.stringify(unit));
}
