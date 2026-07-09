import { ReviewByAuthorSubjectMapper } from "../mappers/ReviewByAuthorSubjectMapper.js";
import type {
  Review_skip_id_,
  Review_skip_value_,
  AuthorSubjectKey,
  Review,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ReviewsByAuthorSubjectResourceInputs extends SharedCollections {
  readonly reviews: EagerCollection<Review_skip_id_, Review_skip_value_>;
}

export class ReviewsByAuthorSubjectResource implements Resource<ReviewsByAuthorSubjectResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ReviewsByAuthorSubjectResourceInputs,
    _context: Context,
  ): EagerCollection<AuthorSubjectKey, Review_skip_id_> {
    const reviewsByAuthorSubject = inputs.reviews.map(
      ReviewByAuthorSubjectMapper,
    );
    return reviewsByAuthorSubject;
  }
}
