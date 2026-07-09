import type { Tag_skip_id_, Tag_skip_value_, Tag } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListTagsResourceInputs extends SharedCollections {
  readonly tags: EagerCollection<Tag_skip_id_, Tag_skip_value_>;
}

export class ListTagsResource implements Resource<ListTagsResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListTagsResourceInputs,
    _context: Context,
  ): EagerCollection<Tag_skip_id_, Tag_skip_value_> {
    return inputs.tags;
  }
}
