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

import java.time.DateTimeException;
import java.time.ZonedDateTime;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Iterator;
import java.util.TreeMap;
import java.util.Map.Entry;

import com.google.gson.*;
import com.google.gson.internal.LazilyParsedNumber;

public final class DataComparator implements Comparator<JsonElement> {

	private DataComparator() {
	}
	
	private enum DType {
		// java null
		DT_JNULL,
		// JsonNull
		DT_NULL,
		DT_BOOL,
		DT_LONG,
		DT_BOXED_LONG,
		DT_DOUBLE,
		DT_STRING,
		DT_REC,
		DT_COLL,
		// Lazily parsed number
		DT_LAZYNUM
	}
		
	
	private static DType getType(JsonElement obj) {
		if(obj == null) {
			return DType.DT_JNULL;
		} else if(obj.isJsonNull()) {
			return DType.DT_NULL;
		} else if(obj.isJsonPrimitive()) {
			final JsonPrimitive prim = obj.getAsJsonPrimitive();
			if(prim.isBoolean()) {
				return DType.DT_BOOL;
			} else if(prim.isString()) {
				return DType.DT_STRING;
			} else if(prim.isNumber()) {
				final Number num = prim.getAsNumber();
				if (num instanceof LazilyParsedNumber) {
				    return DType.DT_LAZYNUM;
				} else if(num instanceof Long || num instanceof Short || num instanceof Integer) {
				    return DType.DT_LONG;
				} else if(num instanceof Double || num instanceof Short || num instanceof Float) {
				    return DType.DT_DOUBLE;
				} else {
				    throw new RuntimeException("Unknown primitive json number type: " + num + " of type " + num.getClass());
				}
			} else {
				throw new RuntimeException("Unknown primitive json type: " + prim);
			}
		} else if(obj.isJsonArray()) {
			return DType.DT_COLL;
		} else if(obj.isJsonObject()) {
		        if(((JsonObject) obj).has("nat")) { return DType.DT_BOXED_LONG; }
			else { return DType.DT_REC;}
		} else {
			throw new RuntimeException("Unknown json type: " + obj + " of type " + obj.getClass());
		}	
	}

	private static TreeMap<String, JsonElement> recToTreeMap(JsonObject obj) {
		final TreeMap<String, JsonElement> dst = new TreeMap<String, JsonElement>();
		for(Entry<String, JsonElement> entry : obj.entrySet()) {
			dst.put(entry.getKey(), entry.getValue());
		}
		return dst;		
	}
	
	private static int compareKeys (Iterator<String> keys1, Iterator<String> keys2) {
		while(keys1.hasNext()) {
			if(! keys2.hasNext()) {
				return 1;
			}
			String k1 = keys1.next();
			String k2 = keys2.next();
			int kcompare = k1.compareTo(k2);
			if(kcompare != 0) {
				return kcompare;
			}
		}
		if(keys2.hasNext()) {
			return -1;
		} else {
			return 0;
		}
	}
	
	/*
	 * We need the comparison to be transitive, which makes this a bit tricky.
	 * We could probably do this without the intermediate map,
	 * but this is simpler and suffices for now.
	 */
	public int compare(JsonObject o1, JsonObject o2) {
		final int sizeCompare = Integer.compare(o1.size(), o2.size());
		if(sizeCompare != 0) {
			return sizeCompare;
		}
		
		TreeMap<String, JsonElement> map1 = recToTreeMap(o1);
		TreeMap<String, JsonElement> map2 = recToTreeMap(o2);
		
		// it is important for transitivity that the keys are sorted first, 
		// which the TreeMap does for us
		final int keyComp = compareKeys(map1.keySet().iterator(), map2.keySet().iterator());
		if(keyComp != 0) {
			return keyComp;
		} else {
			// they have identical keys
		}
		
		Iterator<Entry<String, JsonElement>> iter1 = map1.entrySet().iterator();
		Iterator<Entry<String, JsonElement>> iter2 = map2.entrySet().iterator();
		while(iter1.hasNext()) {
			assert(iter2.hasNext());
			Entry<String, JsonElement> entry1 = iter1.next();
			Entry<String, JsonElement> entry2 = iter2.next();
			assert(entry1.getKey().equals(entry2.getKey()));
			int elemcomp = this.compare(entry1.getValue(), entry2.getValue());
			if(elemcomp != 0) {
				return elemcomp;
			}
		}
		// if we made it through, then they are equal.
		return 0;
	}

	public int compare(JsonArray o1, JsonArray o2) {
		final int len1 = o1.size();
		final int len2 = o2.size();
		final int sizeCompare = Integer.compare(len1, len2);
		if(sizeCompare != 0) {
			return sizeCompare;
		}

		// the lengths are equal
		final JsonElement[] arr1 = RuntimeUtils.collAsArray(o1);
		final JsonElement[] arr2 = RuntimeUtils.collAsArray(o2);
		Arrays.sort(arr1, this);
		Arrays.sort(arr2, this);
		for(int i = 0; i < arr1.length; i ++) {
			final JsonElement elem1 = arr1[i];
			final JsonElement elem2 = arr2[i];
			final int elemcomp = compare(elem1, elem2);
			if(elemcomp != 0) {
				return elemcomp;
			}
		}
		return 0;
	}

	/** Note: this comparator
	 * imposes orderings that are inconsistent with equals.
	 */
	@Override
	public int compare(JsonElement o1, JsonElement o2) {
		// short-circuit in this case
		if(o1 == o2) {
			return 0;
		}

		DType typ1 = getType(o1);
		DType typ2 = getType(o2);

		// For lazily parsed numbers, check type of other operand and try and coerce
		if (typ1 == DType.DT_LAZYNUM) {
		    switch (typ2) {
		    case DT_LONG:
		        return Long.compare(o1.getAsLong(),o2.getAsLong());
		    case DT_BOXED_LONG:
 	 	        return Long.compare(((JsonObject) o1).get("nat").getAsLong(),
					    ((JsonObject) o2).get("nat").getAsLong());
		    case DT_DOUBLE:
			return Double.compare(o1.getAsDouble(), o2.getAsDouble());
		    case DT_LAZYNUM:
			// Tricky here... there is no way to know what to coerce to,
			// underlying gson code relies on string equality, hence so do we
			typ1 = DType.DT_STRING;
			typ2 = DType.DT_STRING;
		    }
		} else if (typ2 == DType.DT_LAZYNUM) {
		    switch (typ1) {
		    case DT_LONG:
		        return Long.compare(o1.getAsLong(),o2.getAsLong());
		    case DT_BOXED_LONG:
 	 	        return Long.compare(((JsonObject) o1).get("nat").getAsLong(),
					    ((JsonObject) o2).get("nat").getAsLong());
		    case DT_DOUBLE:
			return Double.compare(o1.getAsDouble(), o2.getAsDouble());
		    }
		}

		final int typCompare = typ1.compareTo(typ2);
		if(typCompare != 0) {
			return typCompare;
		}

		switch (typ1) {
		case DT_JNULL:
		case DT_NULL:
			return 0;
		case DT_BOOL:
			return Boolean.compare(o1.getAsBoolean(), o2.getAsBoolean());
		case DT_STRING:
			String str1 = o1.getAsString();
			String str2 = o2.getAsString();
			// TODO
			// WARNING 
			// HACK
			// special hack for dates.
			// what could go wrong??? :-D
			// of course, this breaks the transitivity of compareTo
			// sigh...
			// a real solution to this is a bit challenging
			// since we need type information
			// or a wrapper around date times.
			try {
				final ZonedDateTime date1 = ZonedDateTime.parse(str1);
				final ZonedDateTime date2 = ZonedDateTime.parse(str2);
				// if they are both parseable as dates, we will compare them as dates
				return date1.toInstant().compareTo(date2.toInstant());
			} catch(DateTimeException e) {
				// If they are not both parseable as dates, just compare them as strings
				return str1.compareTo(str2); 
			}
		case DT_LONG:
		        return Long.compare(o1.getAsLong(),o2.getAsLong());
		case DT_BOXED_LONG:
 	 	        return Long.compare(((JsonObject) o1).get("nat").getAsLong(),
					    ((JsonObject) o2).get("nat").getAsLong());
		case DT_DOUBLE:
			return Double.compare(o1.getAsDouble(), o2.getAsDouble());
		case DT_COLL:
			return compare(o1.getAsJsonArray(), o2.getAsJsonArray());
		case DT_REC:
			return compare(o1.getAsJsonObject(), o2.getAsJsonObject());
		default:
			// We should never get here.
			// but if we do, we can use toString to give
			// a deterministic order
			return o1.toString().compareTo(o2.toString());
		}
	}
	
	public static DataComparator getComparator() {
		return comparator;
	}
	
	private static final DataComparator comparator = new DataComparator();
	
}
