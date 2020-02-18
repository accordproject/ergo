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

'use strict';

const moment = require('moment-mini');

/**
 * boxing collections
 * @param {*} input - the unboxed input
 * @return {*} the boxed result
 */
function boxColl(input) {
    let result = input;
    if ({}.toString.apply(input) === '[object Array]') {
        const coll = input.map(x => boxColl(x));
        result = {
            $coll: coll,
            $length: input.length
        };
    } else if (typeof input === 'object' && !(input instanceof moment)) {
        if (Object.prototype.hasOwnProperty.call(input,'$class') &&
            !Object.prototype.hasOwnProperty.call(input,'$data')) {
            const theClass = [input.$class];
            const theData = {};
            for (let key in input) {
                if (key !== '$class') {
                    theData[key] = boxColl(input[key]);
                }
            }
            result = {};
            result.$class = theClass;
            result.$data = theData;
        } else {
            result = {};
            for (let key in input) {
                result[key] = boxColl(input[key]);
            }
        }
    }
    return result;
}

/**
 * unboxing collections
 * @param {*} input - the boxed input
 * @return {*} the unboxed result
 */
function unboxColl(input) {
    let result = input;
    if ({}.toString.apply(input) === '[object Array]') {
        result = input.map(x => unboxColl(x));
    } else if (input && typeof input === 'object') {
        if (Object.prototype.hasOwnProperty.call(input,'$coll') &&
            Object.prototype.hasOwnProperty.call(input,'$length')) {
            result = unboxColl(input.$coll.slice(0,input.$length));
        } else if (Object.prototype.hasOwnProperty.call(input,'$class') &&
                   Object.prototype.hasOwnProperty.call(input,'$data') &&
                   !(Object.prototype.hasOwnProperty.call(input.$data,'$left') ||
                     Object.prototype.hasOwnProperty.call(input.$data,'$right') )) {
            for (let key in input.$data) {
                input[key] = unboxColl(input.$data[key]);
            }
            delete input.$data;
            input.$class = unboxColl(input.$class)[0];
        } else {
            for (let key in input) {
                input[key] = unboxColl(input[key]);
            }
        }
    }
    return result;
}

module.exports.boxColl = boxColl;
module.exports.unboxColl = unboxColl;
