import { ReviewBySubjectPreservingIdMapper } from "../mappers/ReviewBySubjectPreservingIdMapper.js";
import type {
  Review_skip_id_,
  Review_skip_value_,
  Subject_skip_id_,
  Review,
  Subject,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ReviewsBySubjectResourceInputs extends SharedCollections {
  readonly reviews: EagerCollection<Review_skip_id_, Review_skip_value_>;
}

export class ReviewsBySubjectResource implements Resource<ReviewsBySubjectResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ReviewsBySubjectResourceInputs,
    _context: Context,
  ): EagerCollection<Subject_skip_id_, Review> {
    const reviewsBySubject = inputs.reviews.map(
      ReviewBySubjectPreservingIdMapper,
    );
    return reviewsBySubject;
  }
}
