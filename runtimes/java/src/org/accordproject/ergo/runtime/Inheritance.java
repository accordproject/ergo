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

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import com.google.gson.*;

public class Inheritance {
	public Inheritance(Map<String, Set<String>> h) {
		this.inheritance = h;
	}

	public Inheritance(JsonArray h) {
		this.inheritance = mkInheritance(h);
	}

	private static Map<String, Set<String>> mkInheritance(JsonArray h) {
		final Map<String, Set<String>> res = new HashMap<String, Set<String>>();
		for(int i = 0; i < h.size(); i ++) {
			final JsonObject elem = h.get(i).getAsJsonObject();
			final String sub = elem.get("sub").getAsString();
			final String sup = elem.get("sup").getAsString();
			Set<String> parentSet = res.get(sub);
			if(parentSet == null) {
				parentSet = new HashSet<String>();
				res.put(sub, parentSet);
			}
			parentSet.add(sup);
		}
		return res;
	}

	/**
	 * returns true if the child can be safely cast to the parent 
	 * @param parent the "Parent" brands
	 * @param child the "Child" brands
	 * @return
	 */
	public boolean isAssignableFrom(Collection<String> parent, Collection<String> child) {
		PARENT: for (final String oneparent : parent) {
			for(String onechild : child) {
				if(onechild.equals(oneparent)) {
					continue PARENT;
				}
				Set<String> childsParents = inheritance.get(onechild);
				if(childsParents != null && childsParents.contains(oneparent)) {
					continue PARENT;
				}
			}
			// if no child claims this parent as an ancestor, then we return false
			return false;
		}
	return true;
	}

	// maps children to parents
	private Map<String, Set<String>> inheritance;
}
