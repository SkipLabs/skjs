import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  LikeKey,
  LikeStored,
  Post_skip_id_,
  Like,
  Post,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each like entry, emit one output pair whose key is sourced from the entry's key's postId field, paired with a new value listing every required field of Like explicitly: postId sourced from the entry's key's postId field (the original Like.postId is encoded into the new output key and also preserved on the value); userId sourced from the entry's key's userId field (the original Like.userId is preserved on the value because the new key carries only postId); createdAt sourced from the entry's value's createdAt field.
export class LikeByPostMapper implements Mapper<
  LikeKey,
  LikeStored,
  Post_skip_id_,
  Like
> {
  mapEntry(
    key: LikeKey,
    values: Values<LikeStored>,
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
