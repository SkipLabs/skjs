import type {
  BookableResource_skip_id_,
  BookableResource_skip_value_,
  BookableResource,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetResourceResourceInputs extends SharedCollections {
  readonly resources: EagerCollection<
    BookableResource_skip_id_,
    BookableResource_skip_value_
  >;
}

export class GetResourceResource implements Resource<GetResourceResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetResourceResourceInputs,
    _context: Context,
  ): EagerCollection<BookableResource_skip_id_, BookableResource_skip_value_> {
    return inputs.resources;
  }
}
