import { ReviewByAuthorPreservingIdMapper } from "../mappers/ReviewByAuthorPreservingIdMapper.js";
import type {
  Review_skip_id_,
  Review_skip_value_,
  User_skip_id_,
  Review,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ReviewsByAuthorResourceInputs extends SharedCollections {
  readonly reviews: EagerCollection<Review_skip_id_, Review_skip_value_>;
}

export class ReviewsByAuthorResource implements Resource<ReviewsByAuthorResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ReviewsByAuthorResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, Review> {
    const reviewsByAuthor = inputs.reviews.map(
      ReviewByAuthorPreservingIdMapper,
    );
    return reviewsByAuthor;
  }
}
