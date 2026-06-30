import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Comment_skip_id_,
  Comment_skip_value_,
  Post_skip_id_,
  PostCommentCount,
  Comment,
  Post,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each comment entry, emit one output pair whose key is sourced from the entry's value's postId field and whose value is the literal one. The original Comment.id is dropped: this collection feeds the SumCommentReducer which only counts occurrences per postId and never needs to identify the source comment row.
export class CommentCountUnitMapper implements Mapper<
  Comment_skip_id_,
  Comment_skip_value_,
  Post_skip_id_,
  PostCommentCount
> {
  mapEntry(
    key: Comment_skip_id_,
    values: Values<Comment_skip_value_>,
    context: Context,
  ): Iterable<[Post_skip_id_, PostCommentCount]> {
    // > body
    const emits: [Post_skip_id_, PostCommentCount][] = [];
    for (const value of values.toArray()) {
      emits.push([value.postId, 1]);
    }
    return emits;
    // < body
  }
}
