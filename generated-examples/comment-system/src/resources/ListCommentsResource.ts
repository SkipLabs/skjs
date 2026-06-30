import { CommentWithLikeCountByThreadKeyMapper } from "../mappers/CommentWithLikeCountByThreadKeyMapper.js";
import type {
  Comment_skip_id_,
  CommentStored,
  ThreadKey,
  LikeIncrement,
  CommentWithLikeCount,
  Comment,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListCommentsResourceInputs extends SharedCollections {
  readonly comments: EagerCollection<Comment_skip_id_, CommentStored>;
  readonly commentsByThreadKey: EagerCollection<ThreadKey, Comment_skip_id_>;
  readonly likeCountByComment: EagerCollection<Comment_skip_id_, LikeIncrement>;
}

export class ListCommentsResource implements Resource<ListCommentsResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListCommentsResourceInputs,
    _context: Context,
  ): EagerCollection<ThreadKey, CommentWithLikeCount> {
    return inputs.commentsByThreadKey.map(
      CommentWithLikeCountByThreadKeyMapper,
      inputs.comments,
      inputs.likeCountByComment,
    );
  }
}
