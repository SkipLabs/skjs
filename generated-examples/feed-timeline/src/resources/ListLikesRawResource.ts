import type { Like_skip_id_, Like_skip_value_, Like } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListLikesRawResourceInputs extends SharedCollections {
  readonly likes: EagerCollection<Like_skip_id_, Like_skip_value_>;
}

export class ListLikesRawResource implements Resource<ListLikesRawResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListLikesRawResourceInputs,
    _context: Context,
  ): EagerCollection<Like_skip_id_, Like_skip_value_> {
    return inputs.likes;
  }
}
