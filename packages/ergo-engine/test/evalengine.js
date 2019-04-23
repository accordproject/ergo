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

const runWorkload = require('./commonengine').runWorkload;
const EvalEngine = require('../lib/evalengine');
const LogicManager = require('@accordproject/ergo-compiler').LogicManager;

describe('#evalengine', () => {
    it('should behave as a proper Eval Engine', () => {
        const engine = new EvalEngine();
        engine.kind().should.equal('eval');
        engine.compileVMScript('const a = 1;').should.not.be.null;
        engine.runVMScriptCall(2,{ a : 1 },'function f() { return context.a + utcOffset; }','f()').should.equal(3);
    });

    it('should cache a script', () => {
        const engine = new EvalEngine();
        const logicManager = new LogicManager('es6', null);
        const script = 'const a = 1';
        logicManager.addLogicFile(script,'test2.js');
        logicManager.compileLogicSync(false);
        const scriptManager = logicManager.getScriptManager();
        engine.cacheJsScript(scriptManager,'test2.js').should.equal(script);
        engine.cacheJsScript(scriptManager,'test2.js').should.equal(script);
    });
});

describe('Execute ES6', () => {
    runWorkload(EvalEngine, 'es6');
});
describe('Execute ES5', () => {
    runWorkload(EvalEngine, 'es5');
});
describe('Execute Cicero', () => {
    runWorkload(EvalEngine, 'cicero');
});

