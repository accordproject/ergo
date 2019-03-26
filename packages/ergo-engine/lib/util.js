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

// Moment serialization function to preserves utcOffset. See https://momentjs.com/docs/#/displaying/as-json/
const momentToJson = function() { return this.format(); };

const Moment = require('moment-mini');
Moment.fn.toJSON = momentToJson;

/**
 * Ensures there is a proper current time
 *
 * @param {string} currentTime - the definition of 'now'
 * @returns {object} if valid, the moment object for the current time
 */
function setCurrentTime(currentTime) {
    if (!currentTime) {
        // Defaults to current local time
        return Moment();
    }
    const now = Moment.parseZone(currentTime, 'YYYY-MM-DDTHH:mm:ssZ', true);
    if (now.isValid()) {
        return now;
    } else {
        throw new Error(`${currentTime} is not a valid moment with the format 'YYYY-MM-DDTHH:mm:ssZ'`);
    }
}

module.exports = { momentToJson, setCurrentTime };
