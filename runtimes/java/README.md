# Notes on (experimental) Java Backend

## Dependencies

You will need a Java 8 compiler and a recent version of ant

## Getting started

Compile the Java runtime for Ergo, from the root ergo directory:

```
bash$ make -C backends/java
```

Compile an Ergo contract to Java

```
bash$ ergoc --target java examples/helloworld/model.cto examples/helloworld/logic.ergo
```

This should create a Java source for your contract (`examples/helloworld/logic.java`)

Compile the resulting Java source
```
bash$ javac -cp backends/java/bin:backends/java/lib/* examples/helloworld/logic.java
```

This should create a class file for your contract (`examples/helloword/logic.class`)

Run the contract

```
bash$ java -cp backends/java/bin:backends/java/lib/*:examples/helloworld org.accordproject.ergo.RunErgo -request examples/helloworld/request.json -state examples/helloworld/state.json -contract examples/helloworld/contract.json logic 
{"left":{"response":{"output":"Hello Fred Blogs (Accord Project)","$class":"org.accordproject.helloworld.Response"},"state":{"$class":"org.accordproject.cicero.contract.AccordContractState","stateId":"1"},"emit":[]}}
```

