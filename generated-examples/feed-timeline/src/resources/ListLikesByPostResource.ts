import { FilterLikesByPostIdMapper } from "../mappers/FilterLikesByPostIdMapper.js";
import type {
  Post_skip_id_,
  Like,
  ListLikesByPostParams,
  Post,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListLikesByPostResourceInputs extends SharedCollections {
  readonly likesByPost: EagerCollection<Post_skip_id_, Like>;
}

export class ListLikesByPostResource implements Resource<ListLikesByPostResourceInputs> {
  private readonly postId: string;

  constructor(params: ListLikesByPostParams) {
    this.postId = params.postId;
  }

  instantiate(
    inputs: ListLikesByPostResourceInputs,
    _context: Context,
  ): EagerCollection<Post_skip_id_, Like> {
    return inputs.likesByPost.map(FilterLikesByPostIdMapper, this.postId);
  }
}
