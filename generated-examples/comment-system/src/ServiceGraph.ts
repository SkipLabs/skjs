import { CommentByThreadKeyMapper } from "./mappers/CommentByThreadKeyMapper.js";
import { CommentLikeByCommentIdMapper } from "./mappers/CommentLikeByCommentIdMapper.js";
import { CommentLikeCountMapper } from "./mappers/CommentLikeCountMapper.js";
import { SumReducer } from "./reducers/SumReducer.js";
import type {
  CommentLike_skip_id_,
  CommentLike,
  CommentLike_skip_value_,
  Comment_skip_id_,
  Comment,
  CommentStored,
  User_skip_id_,
  User,
  User_skip_value_,
  ThreadKey,
  LikeIncrement,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly commentLikes: EagerCollection<
    CommentLike_skip_id_,
    CommentLike_skip_value_
  >;
  readonly comments: EagerCollection<Comment_skip_id_, CommentStored>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly commentLikes: EagerCollection<
    CommentLike_skip_id_,
    CommentLike_skip_value_
  >;
  readonly commentLikesByCommentId: EagerCollection<
    Comment_skip_id_,
    CommentLike
  >;
  readonly comments: EagerCollection<Comment_skip_id_, CommentStored>;
  readonly commentsByThreadKey: EagerCollection<ThreadKey, Comment_skip_id_>;
  readonly likeCountByComment: EagerCollection<Comment_skip_id_, LikeIncrement>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const commentLikesByCommentId = inputs.commentLikes.map(
    CommentLikeByCommentIdMapper,
  );
  const commentsByThreadKey = inputs.comments.map(CommentByThreadKeyMapper);
  const likeCountPerComment = inputs.commentLikes.map(CommentLikeCountMapper);
  const likeCountByComment = likeCountPerComment.reduce(SumReducer);
  const output_commentLikes = inputs.commentLikes;
  const output_commentLikesByCommentId = commentLikesByCommentId;
  const output_comments = inputs.comments;
  const output_commentsByThreadKey = commentsByThreadKey;
  const output_likeCountByComment = likeCountByComment;
  const output_users = inputs.users;
  return {
    commentLikes: output_commentLikes,
    commentLikesByCommentId: output_commentLikesByCommentId,
    comments: output_comments,
    commentsByThreadKey: output_commentsByThreadKey,
    likeCountByComment: output_likeCountByComment,
    users: output_users,
  };
}
