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

const index = require('../index');

const chai = require('chai');

chai.should();
chai.use(require('chai-things'));
chai.use(require('chai-as-promised'));

describe('Module', () => {

    describe('#exports', () => {

        it('should export classes', () => {
            index.APModelManager.should.not.be.null;
            index.Compiler.should.not.be.null;
            index.CompilerException.should.not.be.null;
            index.LogicManager.should.not.be.null;
            index.Logger.should.not.be.null;
            index.ScriptManager.should.not.be.null;
            index.TypeException.should.not.be.null;
            index.Util.should.not.be.null;
            index.FileLoader.should.not.be.null;
            index.ErgoLoader.should.not.be.null;
            index.version.should.not.be.null;
        });
    });
});