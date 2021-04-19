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

/**
 * Ergo Compiler - the core compiler for the Ergo language
 * @module ergo-compiler
 */

module.exports.APModelManager = require('./lib/apmodelmanager.js');
module.exports.Compiler = require('./lib/compiler.js');
module.exports.CompilerException = require('./lib/compilerexception.js');
module.exports.LogicManager = require('./lib/logicmanager.js');
module.exports.Logger = require('@accordproject/concerto-core').Logger;
module.exports.ScriptManager = require('./lib/scriptmanager.js');
module.exports.TypeException = require('./lib/typeexception.js');
module.exports.FileLoader = require('./lib/fileloader.js');
module.exports.ErgoLoader = require('./lib/ergoloader.js');
module.exports.version = require('./package.json');
