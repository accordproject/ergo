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
