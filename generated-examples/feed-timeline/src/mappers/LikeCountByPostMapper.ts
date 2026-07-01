import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Like_skip_id_,
  Like_skip_value_,
  Post_skip_id_,
  CountValue,
  Like,
  Post,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each like entry, emit one output pair whose key is sourced from the entry's key's postId field, and whose value is the literal one. Downstream reducer sums per postId to obtain the like count. The original Like.postId is encoded into the new key (the output key IS Like.postId). userId is dropped: this collection aggregates counts per postId and does not need to identify the source user.
export class LikeCountByPostMapper implements Mapper<
  Like_skip_id_,
  Like_skip_value_,
  Post_skip_id_,
  CountValue
> {
  mapEntry(
    key: Like_skip_id_,
    values: Values<Like_skip_value_>,
    context: Context,
  ): Iterable<[Post_skip_id_, CountValue]> {
    // > body
    const emits: [Post_skip_id_, CountValue][] = [];
    for (const _ of values.toArray()) {
      emits.push([key.postId, 1]);
    }
    return emits;
    // < body
  }
}
