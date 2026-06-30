import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { AuthorIdKey, Review } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry under the authorId key: when the entry's key does not equal the userId param, emit nothing. Otherwise iterate the values associated with the key and for each value, emit one output pair whose key is the entry's key paired with the value unchanged. (The input collection is the output of ReviewByAuthorMapper, which re-keys reviews from (subjectId, authorId) to authorId — multiple reviews by the same author accumulate under one key, so iteration is required; a singleton-only access would raise on any author with two or more reviews.)
export class FilterReviewsByAuthorIdMapper implements Mapper<
  AuthorIdKey,
  Review,
  AuthorIdKey,
  Review
> {
  constructor(private userId: string) {}

  mapEntry(
    key: AuthorIdKey,
    values: Values<Review>,
    context: Context,
  ): Iterable<[AuthorIdKey, Review]> {
    // > body
    if (key !== this.userId) return [];
    const emits: [AuthorIdKey, Review][] = [];
    for (const value of values.toArray()) {
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
