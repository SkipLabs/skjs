import type { Counter } from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly counter: EagerCollection<0, Counter>;
}

export interface GraphCollections extends SharedCollections {
  readonly counter: EagerCollection<0, Counter>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_counter = inputs.counter;
  return { counter: output_counter };
}
