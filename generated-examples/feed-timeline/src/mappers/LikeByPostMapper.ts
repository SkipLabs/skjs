import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Like_skip_id_,
  Like_skip_value_,
  Post_skip_id_,
  Like,
  Post,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each like entry, emit one output pair whose key is sourced from the entry's key's postId field, and whose value lists every required field of Like explicitly: postId sourced from the entry's key's postId field; userId sourced from the entry's key's userId field; createdAt sourced from the entry's value's createdAt field. The original userId key component is preserved in the value as userId (re-injection required so the api handler can reconstruct full Like entities when consulting by postId).
export class LikeByPostMapper implements Mapper<
  Like_skip_id_,
  Like_skip_value_,
  Post_skip_id_,
  Like
> {
  mapEntry(
    key: Like_skip_id_,
    values: Values<Like_skip_value_>,
    context: Context,
  ): Iterable<[Post_skip_id_, Like]> {
    // > body
    const emits: [Post_skip_id_, Like][] = [];
    for (const value of values.toArray()) {
      emits.push([
        key.postId,
        {
          postId: key.postId,
          userId: key.userId,
          createdAt: value.createdAt,
        },
      ]);
    }
    return emits;
    // < body
  }
}
