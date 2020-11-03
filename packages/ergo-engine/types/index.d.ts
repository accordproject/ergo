/// <reference types="vm2" />
/// <reference types="@accordproject/ergo-compiler" />

import { VMScript } from 'vm2'
import { ScriptManager, LogicManager } from '@accordproject/ergo-compiler'

declare const version: string

declare interface TriggerOutput {
  clause: string;
  request: any;
  response: any;
  state: any;
  emit: any;
}

declare interface InvokeOutput {
  clause: string;
  params: any;
  response: any;
  state: any;
  emit: any;
}

declare class Engine {
  kind(): string;
  compileVMScript(script: string): void;
  runVMScriptCall(utcOffset: number, now: any, options: any, context: any, script: any, call: any): void;
  clearCacheJsScript(): void;
  cacheJsScript(scriptManager: ScriptManager, contractId: string): VMScript;
  trigger(logic: LogicManager, contractId: string, contract: any, request: any, state: any, currentTime: string, options: any): TriggerOutput;
  invoke(logic: LogicManager, contractId: string, clauseName: string, contract: any, params: any, state: any, currentTime: string, options: any): InvokeOutput;
  init(logic: LogicManager, contractId: string, contract: any, params: any, currentTime: string, options: any): InvokeOutput;
  calculate(logic: LogicManager, contractId: string, name: string, contract: any, currentTime: string, options: any): InvokeOutput;
  compileAndInit(logic: LogicManager, contract: any, params: any, currentTime: string, options: any): Promise<InvokeOutput>;
  compileAndCalculate(logic: LogicManager, name: string, contract: any, currentTime: string, options: any): Promise<InvokeOutput>;
  compileAndInvoke(logic: LogicManager, clauseName: string, contract: any, params: any, state: any, currentTime: string, options: any): Promise<InvokeOutput>;
  compileAndTrigger(logic: LogicManager, contract: any, request: any, state: any, currentTime: string, options: any): Promise<TriggerOutput>;
}

declare class VMEngine extends Engine {
  kind(): 'vm2';
  compileVMScript(script: string): VMScript;
  runVMScriptCall(utcOffset: number, now: any, options: any, context: any, script: any, call: any): any;
}

export {
  Engine,
  VMEngine,
  version,
}

declare module '@accordproject/ergo-engine' {
  export {
    Engine,
    VMEngine,
    version,
  }
}