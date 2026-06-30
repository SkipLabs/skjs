import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ReviewKey,
  ReviewStored,
  SubjectIdKey,
  RatingValue,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each review entry, emit one output pair whose key is sourced from the entry's key.subjectId field and whose value is sourced from the entry's value.rating field. The original key.subjectId is encoded into the new key (the new key is the subjectId value itself). The original key.authorId is dropped: this collection feeds the RatingSummaryReducer which aggregates per subjectId to produce count/sum/histogram statistics and never needs to identify the source review row, so the authorId component carries no information downstream.
export class RatingContributionMapper implements Mapper<
  ReviewKey,
  ReviewStored,
  SubjectIdKey,
  RatingValue
> {
  mapEntry(
    key: ReviewKey,
    values: Values<ReviewStored>,
    context: Context,
  ): Iterable<[SubjectIdKey, RatingValue]> {
    // > body
    const emits: [SubjectIdKey, RatingValue][] = [];
    for (const value of values.toArray()) {
      emits.push([key.subjectId, value.rating]);
    }
    return emits;
    // < body
  }
}
