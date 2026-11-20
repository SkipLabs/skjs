import { ImportedCtor as Date } from "./declarations.js";

export class Derived extends Date {}

export function construct(): number {
  return new Date().value;
}

export function narrow(x: unknown): number {
  if (x instanceof Date) {
    return x.value;
  }
  return 0;
}
