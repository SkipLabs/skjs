import { CommentCountByPostMapper } from "./mappers/CommentCountByPostMapper.js";
import { CommentsByPostMapper } from "./mappers/CommentsByPostMapper.js";
import { SumReducer } from "./reducers/SumReducer.js";
import type {
  Comment_skip_id_,
  Comment,
  Comment_skip_value_,
  Post_skip_id_,
  Post,
  PostStored,
  User_skip_id_,
  User,
  User_skip_value_,
  CommentCount,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly comments: EagerCollection<Comment_skip_id_, Comment_skip_value_>;
  readonly posts: EagerCollection<Post_skip_id_, PostStored>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly commentCountByPost: EagerCollection<Post_skip_id_, CommentCount>;
  readonly comments: EagerCollection<Comment_skip_id_, Comment_skip_value_>;
  readonly commentsByPost: EagerCollection<Post_skip_id_, Comment>;
  readonly posts: EagerCollection<Post_skip_id_, PostStored>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const commentCountByPostMapped = inputs.comments.map(
    CommentCountByPostMapper,
  );
  const commentCountByPost = commentCountByPostMapped.reduce(SumReducer);
  const commentsByPost = inputs.comments.map(CommentsByPostMapper);
  const output_commentCountByPost = commentCountByPost;
  const output_comments = inputs.comments;
  const output_commentsByPost = commentsByPost;
  const output_posts = inputs.posts;
  const output_users = inputs.users;
  return {
    commentCountByPost: output_commentCountByPost,
    comments: output_comments,
    commentsByPost: output_commentsByPost,
    posts: output_posts,
    users: output_users,
  };
}
