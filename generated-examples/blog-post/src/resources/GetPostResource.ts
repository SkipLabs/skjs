import { AssemblePostMapper } from "../mappers/AssemblePostMapper.js";
import type { Post_skip_id_, Post_skip_value_, Post } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetPostResourceInputs extends SharedCollections {
  readonly posts: EagerCollection<Post_skip_id_, Post_skip_value_>;
}

export class GetPostResource implements Resource<GetPostResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetPostResourceInputs,
    _context: Context,
  ): EagerCollection<Post_skip_id_, Post> {
    return inputs.posts.map(AssemblePostMapper);
  }
}
