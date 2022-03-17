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

let path = require('path');
const webpack = require('webpack');
const packageJson = require('./package.json');

module.exports = {
    entry: {
        client: [
            './index.dist.js'
        ]
    },
    output: {
        path: path.join(__dirname, 'umd'),
        filename: 'ergo-engine.js',
        library: {
            name: 'ergo-engine',
            type: 'umd',
        },
        umdNamedDefine: true,
    },
    plugins: [
        new webpack.BannerPlugin(`Ergo v${packageJson.version}
        Licensed under the Apache License, Version 2.0 (the "License");
        you may not use this file except in compliance with the License.
        You may obtain a copy of the License at
        http://www.apache.org/licenses/LICENSE-2.0
        Unless required by applicable law or agreed to in writing, software
        distributed under the License is distributed on an "AS IS" BASIS,
        WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
        See the License for the specific language governing permissions and
        limitations under the License.`),
        new webpack.DefinePlugin({
            'process.env': {
                'NODE_ENV': JSON.stringify('production')
            }
        })
    ],
    module: {
        rules: [
            {
                test: /\.js$/,
                include: [path.join(__dirname, 'lib')],
                use: ['babel-loader']
            },
            {
                test: /\.ne$/,
                use:['raw-loader']
            }
        ]
    },
    resolve: {
        fallback: {
            'fs': false,
            'tls': false,
            'net': false,
            'path': false,
            'os': false,
            'util': false,
            'url': false,
            'assert': require.resolve('assert/'),
            'constants': require.resolve('constants-browserify'),
            'stream': require.resolve('stream-browserify'),
        }
    }
};