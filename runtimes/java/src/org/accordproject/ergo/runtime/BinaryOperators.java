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

import java.time.Duration;
import java.time.ZonedDateTime;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map.Entry;

import com.google.gson.*;

public class BinaryOperators {
	static JsonPrimitive toLong(long e) {
		return new JsonPrimitive(new Long(e));
	}
	
	static double asDouble(JsonElement e) {
		return e.getAsDouble();
	}
	
	static JsonPrimitive toDouble(double e) {
		return new JsonPrimitive(new Double(e));
	}
	
	static JsonArray asColl(JsonElement e) {
		return e.getAsJsonArray();
	}

	static JsonObject asRec(JsonElement e) {
		return e.getAsJsonObject();
	}

	static Collection<JsonElement> collToCollection(JsonArray coll) {
		final ArrayList<JsonElement> dst = new ArrayList<JsonElement>(coll.size());
		for(final JsonElement elem : coll) {
			dst.add(elem);
		}
		return dst;
	}

	public static JsonElement plus(JsonElement e1, JsonElement e2) {
		return toLong(RuntimeUtils.asLong(e1)+RuntimeUtils.asLong(e2));
	}
	public static JsonElement minus(JsonElement e1, JsonElement e2) {
		return toLong(RuntimeUtils.asLong(e1)-RuntimeUtils.asLong(e2));
	}
	public static JsonElement mult(JsonElement e1, JsonElement e2) {
		return toLong(RuntimeUtils.asLong(e1)*RuntimeUtils.asLong(e2));
	}
	public static JsonElement divide(JsonElement e1, JsonElement e2) {
		return toLong(RuntimeUtils.asLong(e1)/RuntimeUtils.asLong(e2));
	}
	public static JsonElement rem(JsonElement e1, JsonElement e2) {
		return toLong(RuntimeUtils.asLong(e1)%RuntimeUtils.asLong(e2));
	}
	public static JsonElement min(JsonElement e1, JsonElement e2) {
		return toLong(Math.min(RuntimeUtils.asLong(e1),RuntimeUtils.asLong(e2)));
	}
	public static JsonElement max(JsonElement e1, JsonElement e2) {
		return toLong(Math.max(RuntimeUtils.asLong(e1),RuntimeUtils.asLong(e2)));
	}
	
	public static JsonElement equals(JsonElement e1, JsonElement e2) {
		return new JsonPrimitive(DataComparator.getComparator().compare(e1, e2) == 0);
	}
	
	public static JsonElement union(JsonElement e1, JsonElement e2) {
		final JsonArray dst = new JsonArray();
		dst.addAll(e1.getAsJsonArray());
		dst.addAll(e2.getAsJsonArray());
		return dst;
	}
	
	public static JsonElement concat(JsonElement e1, JsonElement e2) {
		final JsonObject rec1 = asRec(e1);
		final JsonObject rec2 = asRec(e2);
		final JsonObject dst = new JsonObject();
		for(final Entry<String, JsonElement> entry : rec1.entrySet()) {
			dst.add(entry.getKey(), entry.getValue());
		}
		for(final Entry<String, JsonElement> entry : rec2.entrySet()) {
			dst.add(entry.getKey(), entry.getValue());
		}
		return dst;
	}
	
	public static JsonElement mergeConcat(JsonElement e1, JsonElement e2) {
		if(compatibleRecs(asRec(e1), asRec(e2))) {
			return UnaryOperators.coll(concat(e1,e2));
		} else {
			return new JsonArray();
		}
	}
	
	private static boolean compatibleRecsAux(JsonObject rec1, JsonObject rec2){
		DataComparator comp = DataComparator.getComparator();
		for(final Entry<String, JsonElement> entry : rec1.entrySet()) {
			final String key = entry.getKey();
			if(rec2.has(key)) {
				final JsonElement val2 = rec2.get(entry.getKey());
				if(comp.compare(entry.getValue(), val2) != 0) {
					return false;
				}
			}
		}
		return true;
	}

	private static boolean compatibleRecs(JsonObject rec1, JsonObject rec2) {
		if(rec1.size() <= rec2.size()) {
			return compatibleRecsAux(rec1, rec2);
		} else {
			return compatibleRecsAux(rec2, rec1);
		}
	}

	public static JsonElement and(JsonElement e1, JsonElement e2) {
		return new JsonPrimitive(e1.getAsBoolean() && e2.getAsBoolean());
	}
	public static JsonElement or(JsonElement e1, JsonElement e2) {
		return new JsonPrimitive(e1.getAsBoolean() || e2.getAsBoolean());
	}
	
	public static JsonElement lt(JsonElement e1, JsonElement e2) {
		return new JsonPrimitive(RuntimeUtils.asLong(e1) < RuntimeUtils.asLong(e2));
	}
	public static JsonElement le(JsonElement e1, JsonElement e2) {
		return new JsonPrimitive(RuntimeUtils.asLong(e1) <= RuntimeUtils.asLong(e2));
	}

	/**
	 * (Shallow) copies an array.  Note that shallow copying suffices since 
	 * everything is assumed immutable.
	 * @param src
	 * @return
	 */
	public static JsonArray copyArray(JsonArray src) {
		final JsonArray dst = new JsonArray();
		dst.addAll(src);
		return dst;
	}
	
	// TODO: up to here
	public static JsonElement bag_minus(JsonElement e1, JsonElement e2) {
		final DataComparator comp = DataComparator.getComparator();
		// Note that collections are immutable, so we need to copy
		// before removing stuff
		final JsonArray ec1 = copyArray(asColl(e1));
		final JsonArray ec2 = asColl(e2);
		
		for(final JsonElement elem2 : ec2) {
			final Iterator<JsonElement> it = ec1.iterator();
			while(it.hasNext()) {
				JsonElement elem1 = it.next();
				if(comp.compare(elem1, elem2) == 0) {
					it.remove();
				}
			}
		}
		return ec1;
	}
	
	public static JsonElement bag_min(JsonElement e1, JsonElement e2) {
		return bag_minus(e1, bag_minus(e1, e2));
	}
	
	public static JsonElement bag_max(JsonElement e1, JsonElement e2) {
		return union(e1, bag_minus(e2, e1));
	}
	
	public static JsonElement contains(JsonElement e1, JsonElement e2) {
		// Note: we can't use the built in contains operation since
		// we need equality to be determined by our comparator
		final JsonArray ec = asColl(e2);
		final DataComparator comp = DataComparator.getComparator();
		for(JsonElement elem : ec) {
//			if (elem instanceof JsonObject) {
//				elem = RuntimeUtils.toLeft(elem);
//			}
			if(comp.compare(elem, e1) == 0) {
				return new JsonPrimitive(true);
			}
		}
		return new JsonPrimitive(false);
	}
	
	public static JsonElement stringConcat(JsonElement e1, JsonElement e2) {
		return new JsonPrimitive(e1.getAsString() + e2.getAsString());
	}

	public static JsonElement float_plus(JsonElement e1, JsonElement e2) {
		return toDouble(asDouble(e1)+asDouble(e2));
	}
	public static JsonElement float_minus(JsonElement e1, JsonElement e2) {
		return toDouble(asDouble(e1)-asDouble(e2));
	}
	public static JsonElement float_mult(JsonElement e1, JsonElement e2) {
		return toDouble(asDouble(e1)*asDouble(e2));
	}
	public static JsonElement float_divide(JsonElement e1, JsonElement e2) {
		return toDouble(asDouble(e1)/asDouble(e2));
	}
	public static JsonElement float_pow(JsonElement e1, JsonElement e2) {
		return toDouble(Math.pow(asDouble(e1),asDouble(e2)));
	}
	public static JsonElement float_min(JsonElement e1, JsonElement e2) {
		return toDouble(Math.min(asDouble(e1),asDouble(e2)));
	}
	public static JsonElement float_max(JsonElement e1, JsonElement e2) {
		return toDouble(Math.max(asDouble(e1),asDouble(e2)));
	}
	public static JsonElement float_ne(JsonElement e1, JsonElement e2) {
		return new JsonPrimitive(asDouble(e1)!=asDouble(e2));
	}
	public static JsonElement float_lt(JsonElement e1, JsonElement e2) {
		return new JsonPrimitive(asDouble(e1)<asDouble(e2));
	}
	public static JsonElement float_le(JsonElement e1, JsonElement e2) {
		return new JsonPrimitive(asDouble(e1)<=asDouble(e2));
	}
	public static JsonElement float_gt(JsonElement e1, JsonElement e2) {
		return new JsonPrimitive(asDouble(e1)>asDouble(e2));
	}
	public static JsonElement float_ge(JsonElement e1, JsonElement e2) {
		return new JsonPrimitive(asDouble(e1)>=asDouble(e2));
	}

	public static JsonElement atan2(JsonElement y, JsonElement x) {
		return new JsonPrimitive(Math.atan2(y.getAsDouble(), x.getAsDouble()));
	}
	
	public static JsonElement sql_date_plus(JsonElement e1, JsonElement e2) {
		return null;
	}
	public static JsonElement sql_date_minus(JsonElement e1, JsonElement e2) {
		return null;
	}
	public static JsonElement sql_date_ne(JsonElement e1, JsonElement e2) {
		return null;
	}
	public static JsonElement sql_date_lt(JsonElement e1, JsonElement e2) {
		return null;
	}
	public static JsonElement sql_date_le(JsonElement e1, JsonElement e2) {
		return null;
	}
		public static JsonElement sql_date_gt(JsonElement e1, JsonElement e2) {
		return null;
	}
	public static JsonElement sql_date_ge(JsonElement e1, JsonElement e2) {
		return null;
	}
	public static JsonElement sql_date_interval_between(JsonElement e1, JsonElement e2) {
		return null;
	}

}
