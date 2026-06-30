import type { Tag_skip_id_, Tag_skip_value_, Tag } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetTagStoredResourceInputs extends SharedCollections {
  readonly tags: EagerCollection<Tag_skip_id_, Tag_skip_value_>;
}

export class GetTagStoredResource implements Resource<GetTagStoredResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetTagStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Tag_skip_id_, Tag_skip_value_> {
    return inputs.tags;
  }
}
