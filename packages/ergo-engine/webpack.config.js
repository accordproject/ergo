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
            './index.js'
        ]
    },
    output: {
        path: path.join(__dirname, 'umd'),
        filename: 'ergo-engine.js',
        library: 'ergo',
        libraryTarget: 'umd',
        umdNamedDefine: true
    },
    plugins: [
        new webpack.BannerPlugin(`Accord Project, Ergo v${packageJson.version} http://accordproject.org. Copyright 2018-2019, Clause Inc.
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
        }),
        new webpack.IgnorePlugin(/vmengine/),
        new webpack.IgnorePlugin(/ergo-compiler/),
    ],
    module: {
        rules: [
            {
                test: /\.js$/,
                include: [path.join(__dirname, 'lib')],
                exclude: /node_modules\/vm2/,
                use: {
                    loader: 'babel-loader',
                    options: {
                        presets: ['@babel/preset-env']
                    }
                }
            },
            {
                test: /\.ne$/,
                use:['raw-loader']
            }
        ]
    },
    node: {
        fs: 'empty',
        net: 'empty',
        tls: 'empty',
        vm2: 'empty'
    }
};