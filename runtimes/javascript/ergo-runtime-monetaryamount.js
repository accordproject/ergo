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

function monetaryAmountFormat(v,f) {
    return f.replace(/0(.)0((.)(0+))?/gi, function(_a,sep1,_b,sep2,digits){
        const len = digits ? digits.length : 0;
        const vs = v.toFixed(len);
        let res = '';
        if (sep2) {
            const d = vs.substring(vs.length - len);
            res += sep2 + d;
        }
        let i = vs.substring(0,vs.length - (len === 0 ? 0 : len+1));
        while (i.length > 3) {
            res = sep1 + i.substring(i.length - 3) + res;
            i = i.substring(0, i.length - 3);
        }
        return i + res;
    });
}
function codeSymbol(c) {
    switch (c) {
    case 'USD' : return '$';
    case 'EUR' : return '€';
    case 'JPY' : return '¥';
    case 'GBP' : return '£';
    case 'AUD' : return 'A$';
    case 'CAD' : return 'C$';
    case 'CHF' : return 'CHF';
    case 'CNY' : return '元';
    case 'HKD' : return 'HK$';
    case 'NZD' : return 'NZ$';
    case 'KRW' : return '₩';
    case 'SGD' : return 'S$';
    case 'MXN' : return 'MEX$';
    case 'INR' : return '₹';
    case 'RUB' : return '₽';
    case 'ZAR' : return 'R';
    case 'TRY' : return '₺';
    case 'BRL' : return 'R$';
    case 'TWD' : return 'NT$';
    case 'PLN' : return 'zł';
    case 'THB' : return '฿';
    case 'IDR' : return 'Rp';
    case 'HUF' : return 'Ft';
    case 'CZK' : return 'Kč';
    case 'ILS' : return '₪';
    case 'CLP' : return 'CLP$';
    case 'PHP' : return '₱';
    case 'AED' : return 'د.إ';
    case 'COP' : return 'COL$';
    case 'SAR' : return '﷼';
    case 'MYR' : return 'RM';
    case 'RON' : return 'L';
    case 'BGN' : return 'лв.';
    default : return c; // Defaults to ISO code
    }
}
function monetaryCodeFormat(v,f) {
    const code = v.substring(v.length-3);
    return f.replace(/K/gi,codeSymbol(code)).replace(/CCC/gi,code);
}
