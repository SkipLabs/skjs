import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ReviewKey,
  ReviewStored,
  SubjectIdKey,
  Review,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each review entry, emit one output pair whose key is sourced from the entry's key.subjectId field, and whose value is a Review record listing every required field of Review explicitly: subjectId sourced from the entry's key.subjectId field; authorId sourced from the entry's key.authorId field; rating sourced from the entry's value.rating field; createdAt sourced from the entry's value.createdAt field; title present when the entry's value.title field is present, sourced from the entry's value.title field, absent otherwise; body present when the entry's value.body field is present, sourced from the entry's value.body field, absent otherwise; updatedAt present when the entry's value.updatedAt field is present, sourced from the entry's value.updatedAt field, absent otherwise. The original key.authorId is preserved in the value as authorId.
export class ReviewBySubjectMapper implements Mapper<
  ReviewKey,
  ReviewStored,
  SubjectIdKey,
  Review
> {
  mapEntry(
    key: ReviewKey,
    values: Values<ReviewStored>,
    context: Context,
  ): Iterable<[SubjectIdKey, Review]> {
    // > body
    const emits: [SubjectIdKey, Review][] = [];
    for (const value of values.toArray()) {
      const review: Review = {
        subjectId: key.subjectId,
        authorId: key.authorId,
        rating: value.rating,
        createdAt: value.createdAt,
        ...(value.title !== undefined && { title: value.title }),
        ...(value.body !== undefined && { body: value.body }),
        ...(value.updatedAt !== undefined && { updatedAt: value.updatedAt }),
      };
      emits.push([key.subjectId, review]);
    }
    return emits;
    // < body
  }
}
