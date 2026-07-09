import type { Follow_skip_id_, Follow_skip_value_, Follow } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListFollowsResourceInputs extends SharedCollections {
  readonly follows: EagerCollection<Follow_skip_id_, Follow_skip_value_>;
}

export class ListFollowsResource implements Resource<ListFollowsResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListFollowsResourceInputs,
    _context: Context,
  ): EagerCollection<Follow_skip_id_, Follow_skip_value_> {
    return inputs.follows;
  }
}
