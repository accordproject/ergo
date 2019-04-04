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

const Util = require('../lib/util');

const chai = require('chai');

chai.should();
chai.use(require('chai-things'));
chai.use(require('chai-as-promised'));

describe('Initialize current time', () => {
    it('Should succeed for a well-formed date/time', function () {
        const currentTime = Util.setCurrentTime('1970-01-01T00:00:00Z');
        return currentTime.format().should.equal('1970-01-01T00:00:00Z');
    });
    it('Should stringify a date time back with its timezone', function () {
        const currentTime = Util.setCurrentTime('1970-01-01T00:00:00+05:00');
        return JSON.stringify(currentTime).should.equal('"1970-01-01T00:00:00+05:00"');
    });
    it('Should fail for a non-well-formed date/time', function () {
        return (() => Util.setCurrentTime('1970-01-01').format()).should.throw('1970-01-01 is not a valid moment with the format \'YYYY-MM-DDTHH:mm:ssZ\'');
    });
    it('Should not fail when currentTime is null', function () {
        return Util.setCurrentTime(null).format().should.not.be.null;
    });
    it('Should not fail when currentTime is undefined', function () {
        return Util.setCurrentTime(undefined).format().should.not.be.null;
    });
});
