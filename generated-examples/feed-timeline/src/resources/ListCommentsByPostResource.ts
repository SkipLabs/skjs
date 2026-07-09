import { FilterCommentsByPostIdMapper } from "../mappers/FilterCommentsByPostIdMapper.js";
import type {
  Post_skip_id_,
  Comment,
  ListCommentsByPostParams,
  Post,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListCommentsByPostResourceInputs extends SharedCollections {
  readonly commentsByPost: EagerCollection<Post_skip_id_, Comment>;
}

export class ListCommentsByPostResource implements Resource<ListCommentsByPostResourceInputs> {
  private readonly postId: string;

  constructor(params: ListCommentsByPostParams) {
    this.postId = params.postId;
  }

  instantiate(
    inputs: ListCommentsByPostResourceInputs,
    _context: Context,
  ): EagerCollection<Post_skip_id_, Comment> {
    return inputs.commentsByPost.map(FilterCommentsByPostIdMapper, this.postId);
  }
}
