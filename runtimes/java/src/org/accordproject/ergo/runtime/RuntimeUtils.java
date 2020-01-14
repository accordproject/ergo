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

import java.util.*;

import com.google.gson.*;

public class RuntimeUtils {
	public static class CollectionBuilder<T> {
		public CollectionBuilder(Collection<T> coll) {
			this.base = coll;
		}

		public CollectionBuilder() {
			this.base = new ArrayList<T>();
		}
		
		public CollectionBuilder(int capacity) {
			this.base = new ArrayList<T>(capacity);
		}

		public  CollectionBuilder<T> add(T obj) {
			base.add(obj);
			return this;
		}

		public Collection<T> result() {
			return base;
		}

		private Collection<T> base;
	}
	
	public static class JsonObjectBuilder {
 		public JsonObjectBuilder() {
 			this.base = new JsonObject();
 		}
 		
 		public JsonObjectBuilder add(String str, JsonElement elem) {
 			base.add(str, elem);
 			return this;
 		}
 		
 		public JsonObject toJsonObject() {
 			return base;
 		}
 		
 		private JsonObject base;
	}
	
	public static JsonArray createJsonArray(JsonElement... elems) {
 		JsonArray arr = new JsonArray();
 		for(JsonElement elem : elems) {
 			arr.add(elem);
 		}
 		return arr;
 	}
	

	private static JsonObject asRec(Object e) {
		return ((JsonObject)e);
	}

	public static boolean either(JsonElement obj) {
 		final JsonObject rec = obj.getAsJsonObject();
 		if(rec.has("left")) {
 			return true;
 		} else if(rec.has("right")) {
 			return false;
 		} else {
 			throw new RuntimeException("RuntimeUtils.either: Expected an either, but got an " + obj);
		}
	}

	public static JsonElement toLeft(JsonElement obj) {
		return asRec(obj).get("left");
	}

	public static JsonElement toRight(JsonElement obj) {
		return asRec(obj).get("right");
	}

	public static JsonElement[] collAsArray(JsonArray coll) {
		final JsonElement[] arr = new JsonElement[coll.size()];
		for(int i = 0; i < coll.size(); i ++) {
			final JsonElement elem = coll.get(i);
			arr[i] = elem;
		}
		return arr;
	}

	public static long asLong(JsonElement e) {
	    if(e.isJsonObject()) {
		if (((JsonObject) e).has("nat"))
		    return ((JsonObject) e).get("nat").getAsLong();
		else
		    return e.getAsLong();
	    } else
		return e.getAsLong();
	}
	public static boolean asBoolean(JsonElement e) {
		return e.getAsBoolean();
	}
}
