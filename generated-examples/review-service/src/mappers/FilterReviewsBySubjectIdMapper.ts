import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { SubjectIdKey, Review } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry under the subjectId key: when the entry's key does not equal the subjectId param, emit nothing. Otherwise iterate the values associated with the key and for each value, emit one output pair whose key is the entry's key paired with the value unchanged. (The input collection is the output of ReviewBySubjectMapper, which re-keys reviews from (subjectId, authorId) to subjectId — multiple reviews of the same subject accumulate under one key, so iteration is required; a singleton-only access would raise on any subject with two or more reviews.)
export class FilterReviewsBySubjectIdMapper implements Mapper<
  SubjectIdKey,
  Review,
  SubjectIdKey,
  Review
> {
  constructor(private subjectId: string) {}

  mapEntry(
    key: SubjectIdKey,
    values: Values<Review>,
    context: Context,
  ): Iterable<[SubjectIdKey, Review]> {
    // > body
    if (key !== this.subjectId) return [];
    const emits: [SubjectIdKey, Review][] = [];
    for (const value of values.toArray()) {
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
