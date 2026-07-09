import type { Counter } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetCounterResourceInputs extends SharedCollections {
  readonly counter: EagerCollection<0, Counter>;
}

export class GetCounterResource implements Resource<GetCounterResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetCounterResourceInputs,
    _context: Context,
  ): EagerCollection<0, Counter> {
    return inputs.counter;
  }
}
