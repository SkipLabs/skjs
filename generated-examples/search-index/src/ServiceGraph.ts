import { AssemblePostMapper } from "./mappers/AssemblePostMapper.js";
import { AssembleSearchDocumentMapper } from "./mappers/AssembleSearchDocumentMapper.js";
import { PostTagByPostMapper } from "./mappers/PostTagByPostMapper.js";
import { PostTagByTagMapper } from "./mappers/PostTagByTagMapper.js";
import type {
  PostTagKey,
  PostTagStored,
  Post_skip_id_,
  Post,
  PostStored,
  Tag_skip_id_,
  Tag,
  Tag_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  PostIdKey,
  PostTag,
  TagIdKey,
  Post_skip_value_,
  SearchDocument,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly postTags: EagerCollection<PostTagKey, PostTagStored>;
  readonly posts: EagerCollection<Post_skip_id_, PostStored>;
  readonly tags: EagerCollection<Tag_skip_id_, Tag_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly postTagsByPost: EagerCollection<PostIdKey, PostTag>;
  readonly postTagsByTag: EagerCollection<TagIdKey, PostTag>;
  readonly posts: EagerCollection<Post_skip_id_, PostStored>;
  readonly postsAssembled: EagerCollection<Post_skip_id_, Post_skip_value_>;
  readonly searchDocuments: EagerCollection<Post_skip_id_, SearchDocument>;
  readonly tags: EagerCollection<Tag_skip_id_, Tag_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const postTagsByPost = inputs.postTags.map(PostTagByPostMapper);
  const output_postTagsByPost = postTagsByPost;
  const postTagsByTag = inputs.postTags.map(PostTagByTagMapper);
  const output_postTagsByTag = postTagsByTag;
  const output_posts = inputs.posts;
  const output_postsAssembled = inputs.posts.map(
    AssemblePostMapper,
    postTagsByPost,
  );
  const output_searchDocuments = inputs.posts.map(
    AssembleSearchDocumentMapper,
    inputs.users,
    postTagsByPost,
    inputs.tags,
  );
  const output_tags = inputs.tags;
  const output_users = inputs.users;
  return {
    postTagsByPost: output_postTagsByPost,
    postTagsByTag: output_postTagsByTag,
    posts: output_posts,
    postsAssembled: output_postsAssembled,
    searchDocuments: output_searchDocuments,
    tags: output_tags,
    users: output_users,
  };
}
