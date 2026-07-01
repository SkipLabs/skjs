import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Post_skip_id_, Post_skip_value_, Post } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each post entry, when the authorId param is absent, emit the entry unchanged. When the authorId param is present and the entry's value's authorId field equals the authorId param, emit the entry unchanged. Otherwise emit nothing.
export class FilterPostByAuthorMapper implements Mapper<
  Post_skip_id_,
  Post_skip_value_,
  Post_skip_id_,
  Post_skip_value_
> {
  constructor(private authorId: string | null) {}

  mapEntry(
    key: Post_skip_id_,
    values: Values<Post_skip_value_>,
    context: Context,
  ): Iterable<[Post_skip_id_, Post_skip_value_]> {
    // > body
    const emits: [Post_skip_id_, Post_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (this.authorId === null || value.authorId === this.authorId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
