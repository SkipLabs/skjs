import { FilterPostByAuthorMapper } from "../mappers/FilterPostByAuthorMapper.js";
import type {
  Post_skip_id_,
  Post_skip_value_,
  ListPostsParams,
  Post,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListPostsResourceInputs extends SharedCollections {
  readonly postsEnriched: EagerCollection<Post_skip_id_, Post_skip_value_>;
}

export class ListPostsResource implements Resource<ListPostsResourceInputs> {
  private readonly authorId: string | null;

  constructor(params: ListPostsParams) {
    this.authorId = params.authorId ?? null;
  }

  instantiate(
    inputs: ListPostsResourceInputs,
    _context: Context,
  ): EagerCollection<Post_skip_id_, Post_skip_value_> {
    return inputs.postsEnriched.map(FilterPostByAuthorMapper, this.authorId);
  }
}
