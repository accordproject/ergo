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

const Chai = require('chai');

Chai.should();
Chai.use(require('chai-things'));
Chai.use(require('chai-as-promised'));

const buildEngine = require('../lib/buildengine');

describe('#buildengine', () => {
    it('should build a VM engine for ES6', async () => {
        const engine = buildEngine('es6',false);
        engine.kind().should.equal('vm2');
    });

    it('should build a eval engine for ES6', async () => {
        const engine = buildEngine('es6',true);
        engine.kind().should.equal('eval');
    });

    it('should build an engine for WASM', async () => {
        const engine = buildEngine('wasm',false);
        engine.kind().should.equal('wasm');
    });
});
