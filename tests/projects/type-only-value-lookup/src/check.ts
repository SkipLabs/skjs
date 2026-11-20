import type {
  ImportedCtor as Date,
  Tags as console,
  tag,
} from "./declarations.js";
import { ImportedCtor as Reexported, Local } from "./barrel.js";

export type Tag = typeof tag;
export const value: Tag = 2;

export function rejectTypeOnlyImport(): unknown {
  // @ts-expect-error 'Date' cannot be used as a value because it was imported using 'import type'.
  return new Date();
}

export function rejectTypeOnlyReexport(): unknown {
  // @ts-expect-error 'Reexported' cannot be used as a value because it was exported using 'export type'.
  return new Reexported();
}

export function retainAmbientConsole(): void {
  console.log("ambient");
}

export function rejectErasedLocalExport(): unknown {
  // @ts-expect-error 'Local' cannot be used as a value because it was exported using 'export type'.
  return new Local();
}
