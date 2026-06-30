import type { ReviewKey, ReviewStored } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetReviewForSubjectResourceInputs extends SharedCollections {
  readonly reviews: EagerCollection<ReviewKey, ReviewStored>;
}

export class GetReviewForSubjectResource implements Resource<GetReviewForSubjectResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetReviewForSubjectResourceInputs,
    _context: Context,
  ): EagerCollection<ReviewKey, ReviewStored> {
    return inputs.reviews;
  }
}
