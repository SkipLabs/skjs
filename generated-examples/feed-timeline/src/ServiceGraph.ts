import { CommentByPostMapper } from "./mappers/CommentByPostMapper.js";
import { CommentCountByPostMapper } from "./mappers/CommentCountByPostMapper.js";
import { CommentFeedEventMapper } from "./mappers/CommentFeedEventMapper.js";
import { EnrichPostWithCountsMapper } from "./mappers/EnrichPostWithCountsMapper.js";
import { LikeByPostMapper } from "./mappers/LikeByPostMapper.js";
import { LikeCountByPostMapper } from "./mappers/LikeCountByPostMapper.js";
import { LikeFeedEventMapper } from "./mappers/LikeFeedEventMapper.js";
import { PostFeedEventMapper } from "./mappers/PostFeedEventMapper.js";
import { SumReducer } from "./reducers/SumReducer.js";
import type {
  Comment_skip_id_,
  Comment,
  Comment_skip_value_,
  Like_skip_id_,
  Like,
  Like_skip_value_,
  Post_skip_id_,
  Post,
  PostStored,
  User_skip_id_,
  User,
  User_skip_value_,
  FeedEventId,
  FeedEvent,
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
  readonly likes: EagerCollection<Like_skip_id_, Like_skip_value_>;
  readonly posts: EagerCollection<Post_skip_id_, PostStored>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly comments: EagerCollection<Comment_skip_id_, Comment_skip_value_>;
  readonly commentsByPost: EagerCollection<Post_skip_id_, Comment>;
  readonly feedEvents: EagerCollection<FeedEventId, FeedEvent>;
  readonly likes: EagerCollection<Like_skip_id_, Like_skip_value_>;
  readonly likesByPost: EagerCollection<Post_skip_id_, Like>;
  readonly posts: EagerCollection<Post_skip_id_, Post_skip_value_>;
  readonly postsStored: EagerCollection<Post_skip_id_, PostStored>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const postFeedEvents = inputs.posts.map(PostFeedEventMapper);
  const likeFeedEvents = inputs.likes.map(LikeFeedEventMapper);
  const commentFeedEvents = inputs.comments.map(CommentFeedEventMapper);
  const allFeedEvents = postFeedEvents.merge(likeFeedEvents, commentFeedEvents);
  const commentOnesByPost = inputs.comments.map(CommentCountByPostMapper);
  const commentCountByPost = commentOnesByPost.reduce(SumReducer);
  const commentsByPost = inputs.comments.map(CommentByPostMapper);
  const likeOnesByPost = inputs.likes.map(LikeCountByPostMapper);
  const likeCountByPost = likeOnesByPost.reduce(SumReducer);
  const likesByPost = inputs.likes.map(LikeByPostMapper);
  const output_comments = inputs.comments;
  const output_commentsByPost = commentsByPost;
  const output_feedEvents = allFeedEvents;
  const output_likes = inputs.likes;
  const output_likesByPost = likesByPost;
  const output_posts = inputs.posts.map(
    EnrichPostWithCountsMapper,
    likeCountByPost,
    commentCountByPost,
  );
  const output_postsStored = inputs.posts;
  const output_users = inputs.users;
  return {
    comments: output_comments,
    commentsByPost: output_commentsByPost,
    feedEvents: output_feedEvents,
    likes: output_likes,
    likesByPost: output_likesByPost,
    posts: output_posts,
    postsStored: output_postsStored,
    users: output_users,
  };
}
