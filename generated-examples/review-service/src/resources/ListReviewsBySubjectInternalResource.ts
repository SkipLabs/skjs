import type { SubjectIdKey, Review } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListReviewsBySubjectInternalResourceInputs extends SharedCollections {
  readonly reviewsBySubject: EagerCollection<SubjectIdKey, Review>;
}

export class ListReviewsBySubjectInternalResource implements Resource<ListReviewsBySubjectInternalResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListReviewsBySubjectInternalResourceInputs,
    _context: Context,
  ): EagerCollection<SubjectIdKey, Review> {
    return inputs.reviewsBySubject;
  }
}
