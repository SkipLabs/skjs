import { FilterReviewsBySubjectIdMapper } from "../mappers/FilterReviewsBySubjectIdMapper.js";
import type {
  SubjectIdKey,
  Review,
  ListReviewsForSubjectParams,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListReviewsForSubjectResourceInputs extends SharedCollections {
  readonly reviewsBySubject: EagerCollection<SubjectIdKey, Review>;
}

export class ListReviewsForSubjectResource implements Resource<ListReviewsForSubjectResourceInputs> {
  private readonly subjectId: string;

  constructor(params: ListReviewsForSubjectParams) {
    this.subjectId = params.subjectId;
  }

  instantiate(
    inputs: ListReviewsForSubjectResourceInputs,
    _context: Context,
  ): EagerCollection<SubjectIdKey, Review> {
    return inputs.reviewsBySubject.map(
      FilterReviewsBySubjectIdMapper,
      this.subjectId,
    );
  }
}
