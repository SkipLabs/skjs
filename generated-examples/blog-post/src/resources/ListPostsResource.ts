import { FilterPostsMapper } from "../mappers/FilterPostsMapper.js";
import type {
  Post_skip_id_,
  CommentCount,
  PostStored,
  Post_skip_value_,
  PostStatus,
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
  readonly commentCountByPost: EagerCollection<Post_skip_id_, CommentCount>;
  readonly posts: EagerCollection<Post_skip_id_, PostStored>;
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
  ): EagerCollection<Post_skip_id_, Post_skip_value_> {
    return inputs.posts.map(
      FilterPostsMapper,
      inputs.commentCountByPost,
      this.authorId,
      this.status,
      this.tag,
    );
  }
}
