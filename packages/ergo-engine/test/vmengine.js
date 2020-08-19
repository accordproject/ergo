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

const Fs = require('fs');
const Path = require('path');

const Chai = require('chai');
const expect = Chai.expect;

Chai.should();
Chai.use(require('chai-things'));
Chai.use(require('chai-as-promised'));

const runWorkload = require('./commonengine').runWorkload;
const VMEngine = require('../lib/vmengine');
const LogicManager = require('@accordproject/ergo-compiler').LogicManager;

// Set of tests
const workload = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, 'workload.json'), 'utf8'));

describe('#vmengine', () => {
    it('should behave as a proper VM engine', async () => {
        const engine = new VMEngine();
        engine.kind().should.equal('vm2');
        engine.instantiate('const a = 1;').should.not.be.null;
        expect (await engine.invokeCall(2,null,null,{ a : 1 },'class C { static f() { return context.a + utcOffset; } }','C','f')).to.equal(3);
    });

    it('should cache a script', () => {
        const engine = new VMEngine();
        const logicManager = new LogicManager('es6', null);
        const script = 'const a = 1';
        logicManager.addLogicFile(script,'test2.js');
        logicManager.compileLogicSync(false);
        const scriptManager = logicManager.getScriptManager();
        engine.cacheModule(scriptManager,'test2.js').should.not.be.null;
        engine.cacheModule(scriptManager,'test2.js').should.not.be.null;
    });

    it('should clear the cache', () => {
        const engine = new VMEngine();
        const logicManager = new LogicManager('es6', null);
        const script = 'const a = 1';
        logicManager.addLogicFile(script,'test2.js');
        logicManager.compileLogicSync(false);
        const scriptManager = logicManager.getScriptManager();
        engine.cacheModule(scriptManager,'test2.js').should.not.be.null;
        engine.cacheModule(scriptManager,'test2.js').should.not.be.null;
        engine.clearCache();
        engine.cacheModule(scriptManager,'test2.js').should.not.be.null;
    });
});

describe('Execute ES6', () => {
    runWorkload(VMEngine, 'es6', workload);
});
