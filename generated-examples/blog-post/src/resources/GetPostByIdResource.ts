import { EnrichPostWithCommentCountMapper } from "../mappers/EnrichPostWithCommentCountMapper.js";
import type {
  Post_skip_id_,
  CommentCount,
  PostStored,
  Post_skip_value_,
  Post,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetPostByIdResourceInputs extends SharedCollections {
  readonly commentCountByPost: EagerCollection<Post_skip_id_, CommentCount>;
  readonly posts: EagerCollection<Post_skip_id_, PostStored>;
}

export class GetPostByIdResource implements Resource<GetPostByIdResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetPostByIdResourceInputs,
    _context: Context,
  ): EagerCollection<Post_skip_id_, Post_skip_value_> {
    return inputs.posts.map(
      EnrichPostWithCommentCountMapper,
      inputs.commentCountByPost,
    );
  }
}
