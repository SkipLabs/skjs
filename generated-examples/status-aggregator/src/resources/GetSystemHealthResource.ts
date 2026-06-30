import type { SystemHealthAggregate } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetSystemHealthResourceInputs extends SharedCollections {
  readonly systemHealthAggregate: EagerCollection<0, SystemHealthAggregate>;
}

export class GetSystemHealthResource implements Resource<GetSystemHealthResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetSystemHealthResourceInputs,
    _context: Context,
  ): EagerCollection<0, SystemHealthAggregate> {
    return inputs.systemHealthAggregate;
  }
}
