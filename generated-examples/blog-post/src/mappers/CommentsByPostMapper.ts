import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Comment_skip_id_,
  Comment_skip_value_,
  Post_skip_id_,
  Comment,
  Post,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each comment entry, emit one output pair whose key is sourced from the entry's value's postId field and whose value lists every required field of Comment explicitly: id sourced from the entry's key; postId, authorId, body, createdAt, updatedAt sourced from the entry's value.
export class CommentsByPostMapper implements Mapper<
  Comment_skip_id_,
  Comment_skip_value_,
  Post_skip_id_,
  Comment
> {
  mapEntry(
    key: Comment_skip_id_,
    values: Values<Comment_skip_value_>,
    context: Context,
  ): Iterable<[Post_skip_id_, Comment]> {
    // > body
    const emits: [Post_skip_id_, Comment][] = [];
    for (const value of values.toArray()) {
      const comment: Comment = {
        id: key,
        postId: value.postId,
        authorId: value.authorId,
        body: value.body,
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
      };
      emits.push([value.postId, comment]);
    }
    return emits;
    // < body
  }
}
