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

module.exports.ComposerConcerto = require('composer-concerto');

module.exports.Logger = require('./lib/logger.js');
module.exports.Util = require('./lib/util.js');
module.exports.ErgoError = require('./lib/ergoerror.js');
module.exports.APModelManager = require('./lib/apmodelmanager.js');
module.exports.ScriptManager = require('./lib/scriptmanager.js');
module.exports.Compiler = require('./lib/compiler.js');
module.exports.TemplateLogic = require('./lib/templatelogic.js');
module.exports.version = require('./package.json');
