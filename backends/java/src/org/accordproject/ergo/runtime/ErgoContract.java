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

package org.accordproject.ergo.runtime;

import com.google.gson.*;

public interface ErgoContract {
	/**
	 * 
	 * @param inheritance a Map from classes to the set of their ancestors
	 * @param world a ({@link com.google.gson})json encoding of the parameters for initialization of the contract.
	 * @return a ({@link com.google.gson})json encoding of the result of initializing the contract
	 */
	JsonElement init(Inheritance inheritance, JsonElement request);
	/**
	 * 
	 * @param inheritance a Map from classes to the set of their ancestors
	 * @param request a ({@link com.google.gson})json encoding of contract request.
	 * @return a ({@link com.google.gson})json encoding of the result of calling the contract
	 */
	JsonElement main(Inheritance inheritance, JsonElement request);
}
