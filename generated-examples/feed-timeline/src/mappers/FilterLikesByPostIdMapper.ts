import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Post_skip_id_, Like, Post } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry under inputs.likesByPost, when the entry's key equals the postId param, iterate the values associated with the key and for each value emit one output pair whose key is the entry's key and whose value is the value unchanged; otherwise emit nothing. (The input collection is re-keyed from Like to Post_skip_id_ by LikeByPostMapper, so multiple likes accumulate under the same postId key — singleton-only access would raise on any post with two or more likes.)
export class FilterLikesByPostIdMapper implements Mapper<
  Post_skip_id_,
  Like,
  Post_skip_id_,
  Like
> {
  constructor(private postId: string) {}

  mapEntry(
    key: Post_skip_id_,
    values: Values<Like>,
    context: Context,
  ): Iterable<[Post_skip_id_, Like]> {
    // > body
    if (key !== this.postId) return [];
    const emits: [Post_skip_id_, Like][] = [];
    for (const value of values.toArray()) {
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
