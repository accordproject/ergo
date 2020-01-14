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
package org.accordproject.ergo;

/* Standard Libraries */
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

/* GSON to import data */
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

/* Ergo Java runtime */
import org.accordproject.ergo.runtime.Inheritance;
import org.accordproject.ergo.runtime.ErgoContract;
import org.accordproject.ergo.runtime.BinaryOperators;

public class RunErgo {
  // Small load-file method
  private static String readFile(String fileName) throws IOException {
    return new String(Files.readAllBytes(Paths.get(fileName)));
  }

  // Usage
  private static void usage() {
    System.err.println("Ergo Java Runner requires the option -request and -contract and the Java class name.\n"+
                       "Options:\n"+
                       " [-request filename] a JSON object containing the input request\n"+
                       " [-contract filename] a JSON object containing the contract instance\n"+
                       " [-state filename] a JSON object containing the contract state\n");
  }

  // Running the Contract
  public static JsonElement runContract(ErgoContract contract,
                                        JsonElement requestData,
                                        JsonElement contractData,
                                        JsonElement stateData) {
      /* Passes empty class inheritance for now */
      Inheritance inheritance = new Inheritance(new JsonArray());
      JsonObject context = new JsonObject();
      context.add("request", requestData);
      context.add("contract", contractData);
      context.add("state", stateData);
      context.add("emit", new JsonArray());
      return contract.main(inheritance, context);
  }

  // Main
  public static void main(String[] args) throws Exception {
    if(args.length < 3) {
        usage();
    }
    String requestFile = null;
    String contractFile = null;
    String stateFile = null;
    for (int i = 0; i < args.length; i++) {
      String arg = args[i];
      // Must have a -input option for the input JSON
      if ("-request".equals(arg)) { requestFile = args[i+1]; i++; }
      else if ("-contract".equals(arg)) { contractFile = args[i+1]; i++; }
      else if ("-state".equals(arg)) { stateFile = args[i+1]; i++; }
      else {
        JsonElement requestData = new JsonParser().parse(new FileReader(requestFile));
        JsonElement contractData = new JsonParser().parse(new FileReader(contractFile));
        JsonElement stateData = new JsonParser().parse(new FileReader(stateFile));
        final String contractName = arg;
        @SuppressWarnings("unchecked")
        final Class<ErgoContract> contractClass = (Class<ErgoContract>) Class.forName(contractName);
        final ErgoContract contract = contractClass.newInstance();
        JsonElement result = runContract(contract, requestData, contractData, stateData);
        System.out.println(result);
      }
    }
  }
}
