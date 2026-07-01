import { ListPostsMapper } from "../mappers/ListPostsMapper.js";
import type {
  Post_skip_id_,
  Post_skip_value_,
  Post,
  PostStatus,
  ListPostsParams,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListPostsResourceInputs extends SharedCollections {
  readonly posts: EagerCollection<Post_skip_id_, Post_skip_value_>;
}

export class ListPostsResource implements Resource<ListPostsResourceInputs> {
  private readonly authorId: string | null;
  private readonly status: PostStatus | null;
  private readonly tag: string | null;

  constructor(params: ListPostsParams) {
    this.authorId = params.authorId ?? null;
    this.status = params.status ?? null;
    this.tag = params.tag ?? null;
  }

  instantiate(
    inputs: ListPostsResourceInputs,
    _context: Context,
  ): EagerCollection<Post_skip_id_, Post> {
    return inputs.posts.map(
      ListPostsMapper,
      this.status,
      this.authorId,
      this.tag,
    );
  }
}
