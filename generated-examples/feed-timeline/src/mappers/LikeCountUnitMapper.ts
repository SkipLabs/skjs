import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  LikeKey,
  LikeStored,
  Post_skip_id_,
  PostLikeCount,
  Post,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each like entry, emit one output pair whose key is sourced from the entry's key's postId field and whose value is the literal one. The original Like.postId is encoded into the new output key. The original Like.userId is dropped: this collection feeds the SumLikeReducer which only needs to count occurrences per postId and never reads the userId of any individual like. The createdAt of the input value is also dropped for the same reason.
export class LikeCountUnitMapper implements Mapper<
  LikeKey,
  LikeStored,
  Post_skip_id_,
  PostLikeCount
> {
  mapEntry(
    key: LikeKey,
    values: Values<LikeStored>,
    context: Context,
  ): Iterable<[Post_skip_id_, PostLikeCount]> {
    // > body
    const emits: [Post_skip_id_, PostLikeCount][] = [];
    for (const _ of values.toArray()) {
      emits.push([key.postId, 1]);
    }
    return emits;
    // < body
  }
}
