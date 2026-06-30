import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Post_skip_id_, PostStored, Post } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each post entry, when the authorId param is present AND the entry's authorId field does not equal the authorId param, emit nothing. Otherwise emit the entry unchanged.
export class FilterPostByAuthorMapper implements Mapper<
  Post_skip_id_,
  PostStored,
  Post_skip_id_,
  PostStored
> {
  constructor(private authorId: string | null) {}

  mapEntry(
    key: Post_skip_id_,
    values: Values<PostStored>,
    context: Context,
  ): Iterable<[Post_skip_id_, PostStored]> {
    // > body
    const emits: [Post_skip_id_, PostStored][] = [];
    for (const value of values.toArray()) {
      if (this.authorId !== null && value.authorId !== this.authorId) continue;
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
