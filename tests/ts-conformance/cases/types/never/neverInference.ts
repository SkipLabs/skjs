// @lib: es2015
// @strict: true
// @target: es2015

import { array } from "../../../../../examples/src/skjs.ts";

declare function f1<T>(x: T[]): T;

function _(): void {
    const neverArray: never[] = array();

    const a1 = f1(array());  // never
    const a2 = f1(neverArray);  // never
}
