import { FilterPostByIdMapper } from "../mappers/FilterPostByIdMapper.js";
import type {
  Post_skip_id_,
  Post_skip_value_,
  GetPostByIdParams,
  Post,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetPostByIdResourceInputs extends SharedCollections {
  readonly posts: EagerCollection<Post_skip_id_, Post_skip_value_>;
}

export class GetPostByIdResource implements Resource<GetPostByIdResourceInputs> {
  private readonly postId: string;

  constructor(params: GetPostByIdParams) {
    this.postId = params.postId;
  }

  instantiate(
    inputs: GetPostByIdResourceInputs,
    _context: Context,
  ): EagerCollection<Post_skip_id_, Post_skip_value_> {
    return inputs.posts.map(FilterPostByIdMapper, this.postId);
  }
}
