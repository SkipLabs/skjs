import type { Post_skip_id_, Post_skip_value_, Post } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetPostByIdResourceInputs extends SharedCollections {
  readonly postsEnriched: EagerCollection<Post_skip_id_, Post_skip_value_>;
}

export class GetPostByIdResource implements Resource<GetPostByIdResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetPostByIdResourceInputs,
    _context: Context,
  ): EagerCollection<Post_skip_id_, Post_skip_value_> {
    return inputs.postsEnriched;
  }
}
