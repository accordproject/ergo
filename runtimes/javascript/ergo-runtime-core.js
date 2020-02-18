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
function boxNat(v) {
    return { '$nat': v };
}
function unboxNat(v) {
    return v['$nat'];
}
function isNat(v) {
    return Object.prototype.hasOwnProperty.call(v,'$nat');
}
function boxColl(v, len) {
    len = (typeof len !== 'undefined') ?  len : v.length;
    return { '$coll': v, '$length': len };
}
function unboxColl(v) {
    return v['$coll'];
}
function isBoxColl(obj) {
    return (Object.prototype.hasOwnProperty.call(obj,'$coll') &&
            Object.prototype.hasOwnProperty.call(obj,'$length'));
}
function collLength(v) {
    return v['$length'];
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
    var inheritanceUnbox = isBoxColl(inheritance)?unboxColl(inheritance):inheritance;
    for (var i=0; i<inheritanceUnbox.length; i=i+1) {
        bsub = inheritanceUnbox[i].sub;
        bsup = inheritanceUnbox[i].sup;
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
        if (isBoxColl(v1)) {
	          v1 = unboxColl(v1).slice(0, collLength(v1));
	      }
    };
    if (t2 === 'object' && v2 !== null) {
        if (isNat(v2)) { t2 = 'number'; v2 = unboxNat(v2); }
        if (isBoxColl(v2)) {
	          v2 = unboxColl(v2).slice(0, collLength(v2));
	      }
    }
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
    throw new Error('TypeError: recDot(' + member +') called on non-record (' + JSON.stringify(receiver) + ')');
}

/* Array */
function array(...args) {
    return boxColl(Array.of(...args));
}
function arrayLength(v) {
    return boxNat(v.$length);
}
function arrayPush(v1,v2) {
    var content1 = unboxColl(v1);
    if (content1.length !== collLength(v1)) {
	      content1 = content1.slice(0, collLength(length));
    }
    content1.push(v2);
    return boxColl(content1);
}
function arrayAccess(v1,v2) {
    var content1 = unboxColl(v1);
    return content1[unboxNat(v2)];
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

/* Brand */
function brand(b,v) {
    return { '$class' : b, '$data' : v };
}
function unbrand(v) {
    if (typeof v === 'object' && Object.prototype.hasOwnProperty.call(v,'$class') && Object.prototype.hasOwnProperty.call(v,'$data')) {
        return v.$data;
    }
    throw new Error('TypeError: unbrand called on non-object (' + JSON.stringify(v) + ')');
}
function cast(brands,v) {
    var brandsUnbox = isBoxColl(brands) ? unboxColl(brands) : brands;
    var type = isBoxColl(v.$class) ? unboxColl(v.$class) : v.$class;
    if (brandsUnbox.length === 1 && brandsUnbox[0] === 'Any') { /* cast to top of inheritance is built-in */
        return boxLeft(v);
    }
    brands:
    for (var i in brandsUnbox) {
        var b = brandsUnbox[i];
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
function iterColl(b, f) {
    var content = unboxColl(b);
    for (let i = 0; i < collLength(b); i++) {
	      f(content[i]);
    }
}
function distinct(b) {
    var result = [ ];
    var content = unboxColl(b);
    for (var i=0; i < collLength(b); i=i+1) {
        var v = content[i];
        var dup = false;
        for (var j=i+1; j < collLength(b); j=j+1) {
            if (equal(v,content[j])) { dup = true; break; }
        }
        if (!(dup)) { result.push(v); } else { dup = false; }
    }
    return boxColl(result);
}
function singleton(v) {
    var content = unboxColl(v);
    if (collLength(v) === 1) {
        return boxLeft(content[0]);
    } else {
        return boxRight(null); /* Not a singleton */
    }
}
function flatten(aOuter) {
    var result = [ ];
    var aOuterContent = unboxColl(aOuter);
    for (var iOuter=0, nOuter=collLength(aOuter); iOuter<nOuter; iOuter = iOuter+1) {
        var aInner = aOuterContent[iOuter];
        var aInnerContent = unboxColl(aInner);
        for (var iInner=0, nInner=collLength(aInner); iInner<nInner; iInner = iInner+1) {
            result.push(aInnerContent[iInner]);
        }
    }
    return boxColl(result);
}
function union(b1, b2) {
    var content1 = unboxColl(b1);
    var content2 = unboxColl(b2);
    if (content1.length !== collLength(b1)) {
	      content1 = content1.slice(0, collLength(b1));
    }
    for (let i = 0; i < content2.length; i++) {
        content1.push(content2[i]);
    }
    var result = boxColl(content1);
    return result;
}
function minus(b1, b2) {
    var result = [ ];
    var v1 = unboxColl(b1).slice(0, collLength(b1));
    var v2 = unboxColl(b2).slice(0, collLength(b2));
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
    return boxColl(result);
}
function min(b1, b2) {
    var result = [ ];
    var v1 = unboxColl(b1).slice(0, collLength(b1));
    var v2 = unboxColl(b2).slice(0, collLength(b2));
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
    return boxColl(result);
}
function max(b1, b2) {
    var result = [ ];
    var v1 = unboxColl(b1).slice(0, collLength(b1));
    var v2 = unboxColl(b2).slice(0, collLength(b2));
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
    return boxColl(result);
}
function nth(b1, n) {
    var index = n;
    var content = unboxColl(b1);
    if (isNat(n)){
        index = unboxNat(n);
    }
    if (0 <= index && index < collLength(b1)) {
        return boxLeft(content[index]);
    } else {
        return boxRight(null);
    }
}
function count(v) {
    return arrayLength(v);
}
function contains(v, b) {
    var content = unboxColl(b);
    for (var i=0; i<collLength(b); i=i+1) {
        if (equal(v, content[i])) {
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
    if (scl.length === 0) { return b; } // Check for no sorting criteria
    var compareFun = compareOfMultipleCriterias(scl);
    /* Sorting in place leads to inconsistencies, notably as it re-orders the input WM in the middle of processing */
    var result = unboxColl(b).slice(0, collLength(b));
    result.sort(compareFun);
    return boxColl(result);
}
function groupByOfKey(l,k,keysf) {
    var result = [ ];
    l.forEach((x) => {
        if (equal(keysf(x),k)) {
            result.push(x);
        }
    });
    return boxColl(result);
}
function groupByNested(l,keysf) {
    var keys = unboxColl(distinct(boxColl(l.map(keysf))));
    var result = [ ];
    keys.forEach((k) => {
        result.push({ 'keys': k, 'group' : groupByOfKey(l,k,keysf) });
    });
    return result;
}
function groupBy(g,kl,l) {
    l = unboxColl(l).slice(0, collLength(l));
    kl = unboxColl(kl).slice(0, collLength(kl));
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
    return boxColl(result);
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
    var content = unboxColl(v).slice(0, collLength(v));
    return content.join(sep);
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
    var content = unboxColl(b);
    var result = 0;
    for (var i=0; i<collLength(b); i=i+1) {
        result += unboxNat(content[i]);
    }
    return boxNat(result);
}
function natMin(b) {
    var content = unboxColl(b);
    var numbers = [ ];
    for (var i=0; i<collLength(b); i=i+1) {
        numbers.push(unboxNat(content[i]));
    }
    return boxNat(Math.min.apply(Math,numbers));
}
function natMax(b) {
    var content = unboxColl(b);
    var numbers = [ ];
    for (var i=0; i<collLength(b); i=i+1) {
        numbers.push(unboxNat(content[i]));
    }
    return boxNat(Math.max.apply(Math,numbers));
}
function natArithMean(b) {
    var len = collLength(b);
    if (len === 0) {
        return boxNat(0);
    } else {
        return boxNat(Math.floor(unboxNat(natSum(b))/len));
    }
}
function floatOfNat(v) {
    return unboxNat(v);
}

/* Float */
function floatSum(b) {
    var content = unboxColl(b);
    var result = 0;
    for (var i=0; i<collLength(b); i=i+1) {
        result += content[i];
    }
    return result;
}
function floatArithMean(b) {
    var len = collLength(b);
    if (len === 0) {
        return 0;
    } else {
        return floatSum(b)/len;
    }
}
function floatMin(b) {
    var content = unboxColl(b).slice(0, collLength(b));
    return Math.min.apply(Math,content);
}
function floatMax(b) {
    var content = unboxColl(b).slice(0, collLength(b));
    return Math.max.apply(Math,content);
}
function natOfFloat(v) {
    return boxNat(Math.trunc(v));
}
