export as namespace Jura;

export type CompilerConfig = {
    source:string,        /* Source language */
    target:string,        /* Target language */
    contract:string,      /* Contract name */
    clause:string };      /* Clause name */

export type Result = {
    result: string
    };

/** Main compilation call
 * @config specifies the compilation parameters, including source,target,contract,clause
 * @returns the compiled code
 */
export declare function compile(config:CompilerConfig): Result;

