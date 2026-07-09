import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Comment_skip_id_, CommentLike, Comment } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry under inputs.commentLikesByComment, when the entry's key does not equal the commentId param, emit nothing. Otherwise iterate the values associated with the key and for each value, emit one output pair whose key is the entry's key paired with the value unchanged.
export class FilterCommentLikesByCommentMapper implements Mapper<
  Comment_skip_id_,
  CommentLike,
  Comment_skip_id_,
  CommentLike
> {
  constructor(private commentId: string) {}

  mapEntry(
    key: Comment_skip_id_,
    values: Values<CommentLike>,
    context: Context,
  ): Iterable<[Comment_skip_id_, CommentLike]> {
    // > body
    if (key !== this.commentId) return [];
    const emits: [Comment_skip_id_, CommentLike][] = [];
    for (const value of values.toArray()) {
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
