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

describe('Resolve root directory for Cucumber', () => {
    it('Should resolve to given root directory', function () {
        return Util.resolveRootDir({rootdir:'foo/bar'}).should.equal('foo/bar');
    });
    it('Should resolve to \'.\'', function () {
        return Util.resolveRootDir({}).should.equal('.');
    });
});
describe('Compare components corner cases', () => {
    it('Should succeed comparing null against null', function () {
        return (() => Util.compareComponent(null, null)).should.not.throw;
    });
    it('Should fail comparing null against 1', function () {
        return (() => Util.compareComponent(null, 1)).should.throw('expected 1 to equal null');
    });
    it('Should succeed comparing undefined against undefined', function () {
        return (() => Util.compareComponent(undefined, undefined)).should.not.throw;
    });
    it('Should fail comparing null against undefined', function () {
        return (() => Util.compareComponent(null, undefined)).should.throw('expected undefined to equal null');
    });
    it('Should resolve to \'.\'', function () {
        return Util.resolveRootDir({}).should.equal('.');
    });
});
