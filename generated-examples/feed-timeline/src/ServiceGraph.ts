import { CommentByPostMapper } from "./mappers/CommentByPostMapper.js";
import { CommentCountUnitMapper } from "./mappers/CommentCountUnitMapper.js";
import { EnrichPostWithCountsMapper } from "./mappers/EnrichPostWithCountsMapper.js";
import { FeedItemFromCommentMapper } from "./mappers/FeedItemFromCommentMapper.js";
import { FeedItemFromLikeMapper } from "./mappers/FeedItemFromLikeMapper.js";
import { FeedItemFromPostMapper } from "./mappers/FeedItemFromPostMapper.js";
import { LikeByPostMapper } from "./mappers/LikeByPostMapper.js";
import { LikeCountUnitMapper } from "./mappers/LikeCountUnitMapper.js";
import { SumCommentReducer } from "./reducers/SumCommentReducer.js";
import { SumLikeReducer } from "./reducers/SumLikeReducer.js";
import type {
  Comment_skip_id_,
  Comment,
  Comment_skip_value_,
  LikeKey,
  LikeStored,
  Post_skip_id_,
  Post,
  PostStored,
  User_skip_id_,
  User,
  User_skip_value_,
  FeedItemKey,
  FeedItem,
  Like,
  Post_skip_value_,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly comments: EagerCollection<Comment_skip_id_, Comment_skip_value_>;
  readonly likes: EagerCollection<LikeKey, LikeStored>;
  readonly posts: EagerCollection<Post_skip_id_, PostStored>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly comments: EagerCollection<Comment_skip_id_, Comment_skip_value_>;
  readonly commentsByPost: EagerCollection<Post_skip_id_, Comment>;
  readonly feedItems: EagerCollection<FeedItemKey, FeedItem>;
  readonly likes: EagerCollection<LikeKey, LikeStored>;
  readonly likesByPost: EagerCollection<Post_skip_id_, Like>;
  readonly posts: EagerCollection<Post_skip_id_, PostStored>;
  readonly postsEnriched: EagerCollection<Post_skip_id_, Post_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const commentUnitByPost = inputs.comments.map(CommentCountUnitMapper);
  const commentCountByPost = commentUnitByPost.reduce(SumCommentReducer);
  const commentsByPost = inputs.comments.map(CommentByPostMapper);
  const feedFromComments = inputs.comments.map(FeedItemFromCommentMapper);
  const feedFromLikes = inputs.likes.map(FeedItemFromLikeMapper);
  const feedFromPosts = inputs.posts.map(FeedItemFromPostMapper);
  const feedItems = feedFromPosts.merge(feedFromLikes, feedFromComments);
  const likeUnitByPost = inputs.likes.map(LikeCountUnitMapper);
  const likeCountByPost = likeUnitByPost.reduce(SumLikeReducer);
  const likesByPost = inputs.likes.map(LikeByPostMapper);
  const output_comments = inputs.comments;
  const output_commentsByPost = commentsByPost;
  const output_feedItems = feedItems;
  const output_likes = inputs.likes;
  const output_likesByPost = likesByPost;
  const output_posts = inputs.posts;
  const postsEnriched = inputs.posts.map(
    EnrichPostWithCountsMapper,
    likeCountByPost,
    commentCountByPost,
  );
  const output_postsEnriched = postsEnriched;
  const output_users = inputs.users;
  return {
    comments: output_comments,
    commentsByPost: output_commentsByPost,
    feedItems: output_feedItems,
    likes: output_likes,
    likesByPost: output_likesByPost,
    posts: output_posts,
    postsEnriched: output_postsEnriched,
    users: output_users,
  };
}
