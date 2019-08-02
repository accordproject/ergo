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
const VMEngine = require('../lib/vmengine');
const LogicManager = require('@accordproject/ergo-compiler').LogicManager;

describe('#vmengine', () => {
    it('should behave as a proper VM engine', () => {
        const engine = new VMEngine();
        engine.kind().should.equal('vm2');
        engine.compileVMScript('const a = 1;').should.not.be.null;
        engine.runVMScriptCall(2,null,null,{ a : 1 },'function f() { return context.a + utcOffset; }','f()').should.equal(3);
    });

    it('should cache a script', () => {
        const engine = new VMEngine();
        const logicManager = new LogicManager('es6', null);
        const script = 'const a = 1';
        logicManager.addLogicFile(script,'test2.js');
        logicManager.compileLogicSync(false);
        const scriptManager = logicManager.getScriptManager();
        engine.cacheJsScript(scriptManager,'test2.js').should.not.be.null;
        engine.cacheJsScript(scriptManager,'test2.js').should.not.be.null;
    });
});

describe('Execute ES6', () => {
    runWorkload(VMEngine, 'es6');
});
describe('Execute ES5', () => {
    runWorkload(VMEngine, 'es5');
});
describe('Execute Cicero', () => {
    runWorkload(VMEngine, 'cicero');
});

