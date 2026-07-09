import type { Post_skip_id_, Post_skip_value_, Post } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListPostsResourceInputs extends SharedCollections {
  readonly posts: EagerCollection<Post_skip_id_, Post_skip_value_>;
}

export class ListPostsResource implements Resource<ListPostsResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListPostsResourceInputs,
    _context: Context,
  ): EagerCollection<Post_skip_id_, Post_skip_value_> {
    return inputs.posts;
  }
}
