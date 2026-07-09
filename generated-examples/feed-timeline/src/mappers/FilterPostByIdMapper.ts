import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Post_skip_id_, Post_skip_value_, Post } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each post entry, emit the entry unchanged when the entry's key equals the postId param. Otherwise emit nothing.
export class FilterPostByIdMapper implements Mapper<
  Post_skip_id_,
  Post_skip_value_,
  Post_skip_id_,
  Post_skip_value_
> {
  constructor(private postId: string) {}

  mapEntry(
    key: Post_skip_id_,
    values: Values<Post_skip_value_>,
    context: Context,
  ): Iterable<[Post_skip_id_, Post_skip_value_]> {
    // > body
    if (key !== this.postId) return [];
    const emits: [Post_skip_id_, Post_skip_value_][] = [];
    for (const value of values.toArray()) {
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
