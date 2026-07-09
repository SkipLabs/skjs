import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Review_skip_id_,
  Review_skip_value_,
  AuthorSubjectKey,
  Review,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each review entry, emit one output pair whose key is a composite AuthorSubjectKey sourced from the entry's value authorId and subjectId fields, and whose value is the entry's key (the review id). The original review id is preserved in the value; authorId and subjectId are encoded into the new composite key. Used for duplicate-detection to enforce one review per (author, subject) pair.
export class ReviewByAuthorSubjectMapper implements Mapper<
  Review_skip_id_,
  Review_skip_value_,
  AuthorSubjectKey,
  Review_skip_id_
> {
  mapEntry(
    key: Review_skip_id_,
    values: Values<Review_skip_value_>,
    context: Context,
  ): Iterable<[AuthorSubjectKey, Review_skip_id_]> {
    // > body
    const emits: [AuthorSubjectKey, Review_skip_id_][] = [];
    for (const value of values.toArray()) {
      const compositeKey: AuthorSubjectKey = {
        authorId: value.authorId,
        subjectId: value.subjectId,
      };
      emits.push([compositeKey, key]);
    }
    return emits;
    // < body
  }
}
