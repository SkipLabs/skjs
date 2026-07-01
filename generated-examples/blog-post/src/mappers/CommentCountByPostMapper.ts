import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Comment_skip_id_,
  Comment_skip_value_,
  Post_skip_id_,
  CommentCount,
  Comment,
  Post,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each comment entry, emit one output pair whose key is sourced from the entry's value's postId field and whose value is the literal one. The original comment id from the entry's key is dropped because the downstream count reducer only needs the per-postId cardinality.
export class CommentCountByPostMapper implements Mapper<
  Comment_skip_id_,
  Comment_skip_value_,
  Post_skip_id_,
  CommentCount
> {
  mapEntry(
    key: Comment_skip_id_,
    values: Values<Comment_skip_value_>,
    context: Context,
  ): Iterable<[Post_skip_id_, CommentCount]> {
    // > body
    const emits: [Post_skip_id_, CommentCount][] = [];
    for (const value of values.toArray()) {
      emits.push([value.postId, 1]);
    }
    return emits;
    // < body
  }
}
