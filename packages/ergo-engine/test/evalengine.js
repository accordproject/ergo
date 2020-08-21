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

const runWorkload = require('./commonengine').runWorkload;
const EvalEngine = require('../lib/evalengine');
const LogicManager = require('@accordproject/ergo-compiler').LogicManager;

// Set of tests
const workload = JSON.parse(Fs.readFileSync(Path.resolve(__dirname, 'workload_es6.json'), 'utf8'));

describe('#evalengine', () => {
    it('should behave as a proper Eval Engine', () => {
        const engine = new EvalEngine();
        engine.kind().should.equal('eval');
        engine.instantiate('const a = 1;').should.not.be.null;
        engine.invokeCall(2,null,null,{ a : 1 },'class C { static f() { return context.a + utcOffset; } }','C','f').should.equal(3);
        (() => engine.invokeCall(2,null,null,{ a : 1 },'class C { static f() { return context.a + utcOffset; } }',null,'f')).should.throw('Cannot invoke contract without a contract name');
    });

    it('should cache a script', async () => {
        const engine = new EvalEngine();
        const logicManager = new LogicManager('es6', null);
        const script = 'const a = 1';
        logicManager.addLogicFile(script,'test2.js');
        logicManager.compileLogicSync(false);
        const scriptManager = logicManager.getScriptManager();
        let script1 = await engine.cacheModule(scriptManager,'test2.js');
        script1.should.equal(script);
        script1 = await engine.cacheModule(scriptManager,'test2.js');
        script1.should.equal(script);
    });
});

describe('Execute ES6', () => {
    runWorkload(EvalEngine, 'es6', workload);
});
