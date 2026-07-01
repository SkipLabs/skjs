import type {
  Comment_skip_id_,
  Comment,
  Comment_skip_value_,
  Post_skip_id_,
  Post,
  Post_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly comments: EagerCollection<Comment_skip_id_, Comment_skip_value_>;
  readonly posts: EagerCollection<Post_skip_id_, Post_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly comments: EagerCollection<Comment_skip_id_, Comment_skip_value_>;
  readonly posts: EagerCollection<Post_skip_id_, Post_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_comments = inputs.comments;
  const output_posts = inputs.posts;
  const output_users = inputs.users;
  return {
    comments: output_comments,
    posts: output_posts,
    users: output_users,
  };
}
