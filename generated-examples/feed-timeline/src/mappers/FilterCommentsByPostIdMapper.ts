import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Post_skip_id_, Comment, Post } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry under inputs.commentsByPost, when the entry's key equals the postId param, iterate the values associated with the key and for each value emit one output pair whose key is the entry's key and whose value is the value unchanged; otherwise emit nothing. (The input collection is re-keyed from Comment_skip_id_ to Post_skip_id_ by CommentByPostMapper, so multiple comments accumulate under the same postId key — singleton-only access would raise on any post with two or more comments.)
export class FilterCommentsByPostIdMapper implements Mapper<
  Post_skip_id_,
  Comment,
  Post_skip_id_,
  Comment
> {
  constructor(private postId: string) {}

  mapEntry(
    key: Post_skip_id_,
    values: Values<Comment>,
    context: Context,
  ): Iterable<[Post_skip_id_, Comment]> {
    // > body
    if (key !== this.postId) return [];
    const emits: [Post_skip_id_, Comment][] = [];
    for (const value of values.toArray()) {
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
