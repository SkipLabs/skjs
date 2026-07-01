import { CommentByPostMapper } from "../mappers/CommentByPostMapper.js";
import type {
  Comment_skip_id_,
  Comment_skip_value_,
  Post_skip_id_,
  Comment,
  Post,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListCommentsByPostResourceInputs extends SharedCollections {
  readonly comments: EagerCollection<Comment_skip_id_, Comment_skip_value_>;
}

export class ListCommentsByPostResource implements Resource<ListCommentsByPostResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListCommentsByPostResourceInputs,
    _context: Context,
  ): EagerCollection<Post_skip_id_, Comment> {
    const commentsByPost = inputs.comments.map(CommentByPostMapper);
    return commentsByPost;
  }
}
