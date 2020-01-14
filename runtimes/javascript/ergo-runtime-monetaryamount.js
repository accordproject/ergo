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

/* Addendum to the Ergo runtime for monetary amount support */

/* MonetaryAmount Formating */
function monetaryAmountFormat(v,f) {
    return f.replace(/0.0.00?0?/gi, function(a){
        const sep1 = a.charAt(1);
        const sep2 = a.charAt(3);
        const len = a.length-4;
        const vs = v.toFixed(len);
        const d = vs.substring(vs.length - len);
        let res = sep2 + d;
        let i = vs.substring(0,vs.length - (len+1));
        while (i.length > 3) {
            res = sep1 + i.substring(i.length - 3) + res;
            i = i.substring(0, i.length - 3);
        }
        return i + res;
    });
}
function codeSymbol(c) {
    switch (c) {
    case 'EUR' : return '€';
    case 'GBP' : return '£';
    case 'PLN' : return 'zł';
    case 'USD' : return '$';
    case 'JPY' : return '¥';
    default : return c; // Defaults to ISO code
    }
}
function monetaryCodeFormat(v,f) {
    const code = v.substring(v.length-3);
    return f.replace(/K/gi,codeSymbol(code)).replace(/CCC/gi,code);
}
