import { FilterReviewsByAuthorIdMapper } from "../mappers/FilterReviewsByAuthorIdMapper.js";
import type { AuthorIdKey, Review, ListMyReviewsParams } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListMyReviewsResourceInputs extends SharedCollections {
  readonly reviewsByAuthor: EagerCollection<AuthorIdKey, Review>;
}

export class ListMyReviewsResource implements Resource<ListMyReviewsResourceInputs> {
  private readonly userId: string;

  constructor(params: ListMyReviewsParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListMyReviewsResourceInputs,
    _context: Context,
  ): EagerCollection<AuthorIdKey, Review> {
    return inputs.reviewsByAuthor.map(
      FilterReviewsByAuthorIdMapper,
      this.userId,
    );
  }
}
