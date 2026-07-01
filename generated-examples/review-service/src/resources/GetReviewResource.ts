import type { Review_skip_id_, Review_skip_value_, Review } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetReviewResourceInputs extends SharedCollections {
  readonly reviews: EagerCollection<Review_skip_id_, Review_skip_value_>;
}

export class GetReviewResource implements Resource<GetReviewResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetReviewResourceInputs,
    _context: Context,
  ): EagerCollection<Review_skip_id_, Review_skip_value_> {
    return inputs.reviews;
  }
}
