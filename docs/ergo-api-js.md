---
id: ergo-api-js
title: JavaScript API
---

## Classes

<dl>
<dt><a href="#Commands">Commands</a></dt>
<dd><p>Utility class that implements the commands exposed by the Ergo CLI.</p>
</dd>
<dt><a href="#Ergo">Ergo</a></dt>
<dd><p>Utility class that implements the internals for Ergo.</p>
</dd>
<dt><a href="#ErgoEngine">ErgoEngine</a></dt>
<dd><p>Utility class that implements the internals for Ergo.</p>
</dd>
</dl>

<a name="Commands"></a>

## Commands
Utility class that implements the commands exposed by the Ergo CLI.

**Kind**: global class  

* [Commands](#Commands)
    * [.compile(ergoPath, ctoPaths, target, link)](#Commands.compile) ⇒ <code>object</code>
    * [.execute(ergoPath, ctoPaths, contractPath, requestsPath, statePath, contractName)](#Commands.execute) ⇒ <code>object</code>
    * [.parseCTO(ctoPath)](#Commands.parseCTO) ⇒ <code>object</code>
    * [.parseCTOtoFileSync(ctoPath)](#Commands.parseCTOtoFileSync) ⇒ <code>string</code>
    * [.parseCTOtoFile(ctoPath)](#Commands.parseCTOtoFile) ⇒ <code>string</code>

<a name="Commands.compile"></a>

### Commands.compile(ergoPath, ctoPaths, target, link) ⇒ <code>object</code>
Compile Ergo

**Kind**: static method of [<code>Commands</code>](#Commands)  
**Returns**: <code>object</code> - Promise to the compiled JavaScript code  

| Param | Type | Description |
| --- | --- | --- |
| ergoPath | <code>string</code> | path to the Ergo file |
| ctoPaths | <code>string</code> | paths to CTO models |
| target | <code>string</code> | language (javascript|javascript_cicero) |
| link | <code>boolean</code> | to JavaScript runtime |

<a name="Commands.execute"></a>

### Commands.execute(ergoPath, ctoPaths, contractPath, requestsPath, statePath, contractName) ⇒ <code>object</code>
Execute Ergo

**Kind**: static method of [<code>Commands</code>](#Commands)  
**Returns**: <code>object</code> - Promise to the result of execution  

| Param | Type | Description |
| --- | --- | --- |
| ergoPath | <code>string</code> | path to the Ergo file |
| ctoPaths | <code>Array.&lt;string&gt;</code> | paths to CTO models |
| contractPath | <code>string</code> | path to the contract data in JSON |
| requestsPath | <code>Array.&lt;string&gt;</code> | path to the request transaction in JSON |
| statePath | <code>string</code> | path to the state in JSON |
| contractName | <code>string</code> | of the contract to execute |

<a name="Commands.parseCTO"></a>

### Commands.parseCTO(ctoPath) ⇒ <code>object</code>
Parse CTO to JSON

**Kind**: static method of [<code>Commands</code>](#Commands)  
**Returns**: <code>object</code> - The parsed CTO model syntax tree in JSON  

| Param | Type | Description |
| --- | --- | --- |
| ctoPath | <code>string</code> | path to CTO model file |

<a name="Commands.parseCTOtoFileSync"></a>

### Commands.parseCTOtoFileSync(ctoPath) ⇒ <code>string</code>
Parse CTO to JSON File

**Kind**: static method of [<code>Commands</code>](#Commands)  
**Returns**: <code>string</code> - The name of the generated CTOJ model file  

| Param | Type | Description |
| --- | --- | --- |
| ctoPath | <code>string</code> | path to CTO model file |

<a name="Commands.parseCTOtoFile"></a>

### Commands.parseCTOtoFile(ctoPath) ⇒ <code>string</code>
Parse CTO to JSON File

**Kind**: static method of [<code>Commands</code>](#Commands)  
**Returns**: <code>string</code> - The name of the generated CTOJ model file  

| Param | Type | Description |
| --- | --- | --- |
| ctoPath | <code>string</code> | path to CTO model file |

<a name="Ergo"></a>

## Ergo
Utility class that implements the internals for Ergo.

**Kind**: global class  

* [Ergo](#Ergo)
    * [.parseCTOtoJSON(ctoText)](#Ergo.parseCTOtoJSON) ⇒ <code>object</code>
    * [.parseCTO(ctoText)](#Ergo.parseCTO) ⇒ <code>object</code>
    * [.compileToJavaScript(ergoText, ctoTexts, target)](#Ergo.compileToJavaScript) ⇒ <code>string</code>
    * [.compileToJavaScriptAndLink(ergoText, ctoTexts, target)](#Ergo.compileToJavaScriptAndLink) ⇒ <code>object</code>
    * [.compile(ergoText, ctoTexts, target)](#Ergo.compile) ⇒ <code>object</code>
    * [.compileAndLink(ergoText, ctoTexts, target)](#Ergo.compileAndLink) ⇒ <code>object</code>
    * [.linkErgoRuntime(ergoCode)](#Ergo.linkErgoRuntime) ⇒ <code>string</code>
    * [.ergoErrorToString(error)](#Ergo.ergoErrorToString) ⇒ <code>string</code>
    * [.commonCTOs()](#Ergo.commonCTOs) ⇒ <code>Array.&lt;string&gt;</code>

<a name="Ergo.parseCTOtoJSON"></a>

### Ergo.parseCTOtoJSON(ctoText) ⇒ <code>object</code>
Parse CTO to JSON

**Kind**: static method of [<code>Ergo</code>](#Ergo)  
**Returns**: <code>object</code> - The parsed CTO model syntax tree in JSON  

| Param | Type | Description |
| --- | --- | --- |
| ctoText | <code>string</code> | text for CTO model |

<a name="Ergo.parseCTO"></a>

### Ergo.parseCTO(ctoText) ⇒ <code>object</code>
Parse CTO

**Kind**: static method of [<code>Ergo</code>](#Ergo)  
**Returns**: <code>object</code> - The parsed CTO model syntax tree in JSON  

| Param | Type | Description |
| --- | --- | --- |
| ctoText | <code>string</code> | text for CTO model |

<a name="Ergo.compileToJavaScript"></a>

### Ergo.compileToJavaScript(ergoText, ctoTexts, target) ⇒ <code>string</code>
Compile Ergo to JavaScript

**Kind**: static method of [<code>Ergo</code>](#Ergo)  
**Returns**: <code>string</code> - The compiled JavaScript code  

| Param | Type | Description |
| --- | --- | --- |
| ergoText | <code>string</code> | text for Ergo code |
| ctoTexts | <code>Array.&lt;string&gt;</code> | texts for CTO models |
| target | <code>string</code> | language (javascript|javascript_cicero) |

<a name="Ergo.compileToJavaScriptAndLink"></a>

### Ergo.compileToJavaScriptAndLink(ergoText, ctoTexts, target) ⇒ <code>object</code>
Compile and Link Ergo to JavaScript

**Kind**: static method of [<code>Ergo</code>](#Ergo)  
**Returns**: <code>object</code> - Promise to the compiled and linked JavaScript code  

| Param | Type | Description |
| --- | --- | --- |
| ergoText | <code>string</code> | text for Ergo code |
| ctoTexts | <code>Array.&lt;string&gt;</code> | texts for CTO models |
| target | <code>string</code> | language (javascript|javascript_cicero) |

<a name="Ergo.compile"></a>

### Ergo.compile(ergoText, ctoTexts, target) ⇒ <code>object</code>
Compile Ergo

**Kind**: static method of [<code>Ergo</code>](#Ergo)  
**Returns**: <code>object</code> - Promise to the compiled JavaScript code  

| Param | Type | Description |
| --- | --- | --- |
| ergoText | <code>string</code> | text for Ergo code |
| ctoTexts | <code>Array.&lt;string&gt;</code> | texts for CTO models |
| target | <code>string</code> | language (javascript|javascript_cicero) |

<a name="Ergo.compileAndLink"></a>

### Ergo.compileAndLink(ergoText, ctoTexts, target) ⇒ <code>object</code>
Compile and Link Ergo

**Kind**: static method of [<code>Ergo</code>](#Ergo)  
**Returns**: <code>object</code> - Promise to the compiled and linked JavaScript code  

| Param | Type | Description |
| --- | --- | --- |
| ergoText | <code>string</code> | text for Ergo code |
| ctoTexts | <code>Array.&lt;string&gt;</code> | texts for CTO models |
| target | <code>string</code> | language (javascript|javascript_cicero) |

<a name="Ergo.linkErgoRuntime"></a>

### Ergo.linkErgoRuntime(ergoCode) ⇒ <code>string</code>
Link runtime to compiled Ergo code

**Kind**: static method of [<code>Ergo</code>](#Ergo)  
**Returns**: <code>string</code> - compiled Ergo code in JavaScript linked to Ergo runtime  

| Param | Type | Description |
| --- | --- | --- |
| ergoCode | <code>string</code> | compiled Ergo code in JavaScript |

<a name="Ergo.ergoErrorToString"></a>

### Ergo.ergoErrorToString(error) ⇒ <code>string</code>
Error message

**Kind**: static method of [<code>Ergo</code>](#Ergo)  
**Returns**: <code>string</code> - error message  

| Param | Type | Description |
| --- | --- | --- |
| error | <code>object</code> | object returned by Ergo compiler |

<a name="Ergo.commonCTOs"></a>

### Ergo.commonCTOs() ⇒ <code>Array.&lt;string&gt;</code>
Common CTOs

**Kind**: static method of [<code>Ergo</code>](#Ergo)  
**Returns**: <code>Array.&lt;string&gt;</code> - Built-in CTO models  
<a name="ErgoEngine"></a>

## ErgoEngine
Utility class that implements the internals for Ergo.

**Kind**: global class  

* [ErgoEngine](#ErgoEngine)
    * [.executeErgoCode(ergoCode, contractJson, requestJson, stateJson, contractName)](#ErgoEngine.executeErgoCode) ⇒ <code>object</code>
    * [.execute(ergoText, ctoTexts, contractJson, requestJson, stateJson, contractName)](#ErgoEngine.execute) ⇒ <code>object</code>

<a name="ErgoEngine.executeErgoCode"></a>

### ErgoEngine.executeErgoCode(ergoCode, contractJson, requestJson, stateJson, contractName) ⇒ <code>object</code>
Execute compiled Ergo code

**Kind**: static method of [<code>ErgoEngine</code>](#ErgoEngine)  
**Returns**: <code>object</code> - Promise to the result of execution  

| Param | Type | Description |
| --- | --- | --- |
| ergoCode | <code>string</code> | JavaScript code for ergo logic |
| contractJson | <code>object</code> | the contract data in JSON |
| requestJson | <code>object</code> | the request transaction in JSON |
| stateJson | <code>object</code> | the state in JSON |
| contractName | <code>string</code> | of the contract to execute |

<a name="ErgoEngine.execute"></a>

### ErgoEngine.execute(ergoText, ctoTexts, contractJson, requestJson, stateJson, contractName) ⇒ <code>object</code>
Execute Ergo (JavaScript)

**Kind**: static method of [<code>ErgoEngine</code>](#ErgoEngine)  
**Returns**: <code>object</code> - Promise to the result of execution  

| Param | Type | Description |
| --- | --- | --- |
| ergoText | <code>string</code> | text for Ergo code |
| ctoTexts | <code>string</code> | texts for CTO models |
| contractJson | <code>object</code> | the contract data in JSON |
| requestJson | <code>object</code> | the request transaction in JSON |
| stateJson | <code>object</code> | the state in JSON |
| contractName | <code>string</code> | of the contract to execute |



* * *

&copy; Clause Inc.