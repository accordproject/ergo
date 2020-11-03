/// <reference types="node" />
/// <reference types="winston" />
/// <reference types="@accordproject/concerto-core" />

import { Logger, LeveledLogMethod } from 'winston';
import { BaseFileException, Factory, Introspector, ModelManager, Serializer } from '@accordproject/concerto-core'

// Winston logger

declare module 'winston' {
    interface Logger {
        setup(fn: (process: any, env: string, logDir: string) => void): void;
        entry: LeveledLogMethod;
        exit: LeveledLogMethod;
    }
}

// Utils

declare namespace Util {
    function momentToJson(): any;
    function setCurrentTime(currentTime: string): any;
}

// Version

declare const version: string

// Exceptions

declare interface FileLocation {
    start: { line: number, column: number };
    end: { line: number, column: number };
}

declare class CompilerException extends BaseFileException {
    constructor(message: string, fileLocation?: FileLocation, fullMessage?: string, fileName?: string, component?: string);
}

declare class TypeException extends CompilerException {
    constructor(message: string, fileLocation?: FileLocation, fullMessage?: string, fileName?: string, component?: string);
}

// Target

declare type Target = 'cicero' | 'es5' | 'es6' | 'java';

// Source

declare interface Source {
    name: string;
    content: string;
}

// Ergo Input
declare interface Input {
    $class: string;
}

// AP Model Manager

declare abstract class APModelManager extends ModelManager {
    getModels(): { name: string; content: string; }[];
}

// Function Declaration

declare class FunctionDeclaration {
    constructor(
        modelManager: ModelManager,
        language: string,
        name: string,
        visibility: string,
        returnType: string,
        throws: string,
        parameterNames: string[],
        parameterTypes: string[],
        decorators: string[],
        functionText: string
    );
    getFunctionText(): string;
    getThrows(): string;
    getLanguage(): string;
    getDecorators(): string[];
    getVisibility(): string;
    getReturnType(): string;
    getName(): string;
    getParameterNames(): string[];
    getParameterTypes(): string[];
}

// Script

declare class Script {
    constructor(
        modelManager: ModelManager,
        identifier: string,
        language: string,
        contents: string,
        contractName: string
    );
    getIdentifier(): string;
    getContractName(): string;
    getLanguage(): string;
    getContents(): string;
    getFunctionDeclarations(): FunctionDeclaration[];
    getTokens(): any[];
}

// ScriptManager

declare interface ScriptManagerOptions {
    warnings?: boolean
}

declare class ScriptManager {
    constructor(target: Target, modelManager: ModelManager, options: ScriptManagerOptions);
    changeTarget(target: Target, recompile: boolean): void;
    createScript(identifier: string, language: string, contents: string): Script;
    modifyScript(identifier: string, language: string, contents: string): void;
    addTemplateFile(templateFile: string, fileName: string): void
    addScript(script: Script): void;
    updateScript(script: Script): void;
    deleteScript(identifier: string): void;
    getScripts(): Script[];
    getAllScripts(): Script[];
    getCombinedScripts(): string;
    getTargetKind(target: Target): '.js' | '.ergo' | '.java';
    getScriptsForTarget(target: Target): Script[];
    getLogic(): Source[];
    clearScripts(): void;
    private getScript(identifier: string): Script;
    private getCompiledScript(): Script;
    private getCompiledJavaScript(): string;
    getScriptIdentifiers(): string[];
    compileLogic(force: boolean): Script;
    allFunctionDeclarations(): FunctionDeclaration[];
    hasFunctionDeclaration(name: string): void;
    hasDispatch(): void;
    hasInit(): void;

    static _throwCompilerException(error: any): void;
}

// Logic Manager

declare interface LogicManagerOptions {
    warnings?: boolean
}

declare class LogicManager {
    constructor(target: Target, options: LogicManagerOptions);
    getTarget(): Target;
    setTarget(target: Target, recompile: boolean): void;
    setContractName(contractName: string): void;
    getContractName(): string;
    private getDispatchCall(): string;
    private getInvokeCall(clauseName: string): string
    getIntrospector(): Introspector;
    getFactory(): Factory;
    getSerializer(): Serializer;
    getScriptManager(): ScriptManager;
    getModelManager(): ModelManager;
    addLogicFile(logicFile: string, fileName: string): void;
    addTemplateFile(modelFile: string, fileName: string): void;
    addModelFile(modelFile: string, fileName: string): void;
    addModelFiles(modelFiles: string[], modelFileNames?: string[]): void;
    validateModelFiles(): void;
    registerCompiledLogicSync(): void;
    compileLogicSync(force: boolean): Script;
    compileLogic(force: boolean): Promise<void>;
    addErgoBuiltin(): void;
    validateInput(input: any): any;
    validateContract(contract: any, options: any): any;
    validateInputRecord(input: any): any;
    validateOutput(output: any): any;
    validateOutputArray(outputArray: any[]): any[];
    updateModel(content: string, name: string): void;
    updateLogic(content: string, name: string): void;
}

// Compiler

declare class Compiler {
    static parseCTOtoJSON(ctoContent: string): any;
    static contractCallName(contractName: string): string;
    static contractCallNamePromise(contractName: string): string;

    static compileToJavaScript(
        ergoSources: Source[],
        ctoSources: Source[],
        target: string,
        link: boolean,
        warnings: boolean
    ): string;

    static compile(
        ergoSources: Source[],
        ctoSources: Source[],
        target: string,
        link: boolean,
        warnings: boolean
    ): any;

    static ergoErrorToString(error: any): string;
    static ergoVerboseErrorToString(error: any): string;
    static availableTargets(): string[];
    static isValidTarget(target: string): boolean;
}

// File Loader

declare class FileLoader {
    static loadZipFileContents(zip: any, path: string, json?: boolean, required?: boolean): Promise<string>;
    static loadZipFilesContents(zip: any, regex: RegExp): Promise<any[]>;
    static loadZipFileBuffer(zip: any, path: string, required?: boolean): Promise<Buffer>;
    static loadFileContents(path: string, fileName: string, json?: boolean, required?: boolean): Promise<string>;
    static loadFileBuffer(path: string, fileName: string, required?: boolean): Promise<Buffer>;
    static loadFilesContents(path: string, regex: RegExp): Promise<any[]>
    static normalizeNLs(input: string): string;
}

// Ergo Loader

declare class ErgoLoader {
    static fromDirectory(path: string, options: LogicManagerOptions): Promise<LogicManager>;
    static fromZip(buffer: Buffer, options: LogicManagerOptions): Promise<LogicManager>;
    static fromFiles(files: string[], options: LogicManagerOptions): Promise<LogicManager>;
}

// Exports

export {
    TypeException,
    CompilerException,
    APModelManager,
    ScriptManager,
    LogicManager,
    Compiler,
    FileLoader,
    ErgoLoader,
    Util,
    Logger,
    version,
}

declare module '@accordproject/ergo-compiler' {
    export {
        TypeException,
        CompilerException,
        APModelManager,
        ScriptManager,
        LogicManager,
        Compiler,
        FileLoader,
        ErgoLoader,
        Util,
        Logger,
        version,
    }
}
