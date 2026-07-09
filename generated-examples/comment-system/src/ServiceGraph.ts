import { AssembleCommentMapper } from "./mappers/AssembleCommentMapper.js";
import { CommentLikesByCommentMapper } from "./mappers/CommentLikesByCommentMapper.js";
import { LikeCountByCommentMapper } from "./mappers/LikeCountByCommentMapper.js";
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
  Comment_skip_value_,
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
  readonly commentLikesByComment: EagerCollection<
    Comment_skip_id_,
    CommentLike
  >;
  readonly comments: EagerCollection<Comment_skip_id_, CommentStored>;
  readonly commentsAssembled: EagerCollection<
    Comment_skip_id_,
    Comment_skip_value_
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const commentLikesByComment = inputs.commentLikes.map(
    CommentLikesByCommentMapper,
  );
  const likeCountByComment = inputs.commentLikes.map(LikeCountByCommentMapper);
  const commentsAssembled = inputs.comments.map(
    AssembleCommentMapper,
    likeCountByComment,
  );
  const output_commentLikes = inputs.commentLikes;
  const output_commentLikesByComment = commentLikesByComment;
  const output_comments = inputs.comments;
  const output_commentsAssembled = commentsAssembled;
  const output_users = inputs.users;
  return {
    commentLikes: output_commentLikes,
    commentLikesByComment: output_commentLikesByComment,
    comments: output_comments,
    commentsAssembled: output_commentsAssembled,
    users: output_users,
  };
}
