import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Comment_skip_id_,
  Comment_skip_value_,
  Post_skip_id_,
  CountValue,
  Comment,
  Post,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each comment entry, emit one output pair whose key is sourced from the entry's value's postId field, and whose value is the literal one. Downstream reducer sums per postId to obtain the comment count. id is dropped: this collection aggregates counts per postId and does not need to identify the source comment.
export class CommentCountByPostMapper implements Mapper<
  Comment_skip_id_,
  Comment_skip_value_,
  Post_skip_id_,
  CountValue
> {
  mapEntry(
    key: Comment_skip_id_,
    values: Values<Comment_skip_value_>,
    context: Context,
  ): Iterable<[Post_skip_id_, CountValue]> {
    // > body
    const emits: [Post_skip_id_, CountValue][] = [];
    for (const value of values.toArray()) {
      emits.push([value.postId, 1]);
    }
    return emits;
    // < body
  }
}
