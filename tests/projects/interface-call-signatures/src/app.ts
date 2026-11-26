import { Callable, Newable } from "./lib.js";

declare const c: Callable;
declare const n: Newable;

function use(): void {
  const a: number = c("hi");
  const b: string = c(42);
  const x: Newable = new n("hi");
}
