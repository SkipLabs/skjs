import { ProjectSearchDocumentMapper } from "./mappers/ProjectSearchDocumentMapper.js";
import { SearchDocByPostIdMapper } from "./mappers/SearchDocByPostIdMapper.js";
import type {
  Post_skip_id_,
  Post,
  PostStored,
  Tag_skip_id_,
  Tag,
  Tag_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  SearchSortKey,
  SearchDocument,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly posts: EagerCollection<Post_skip_id_, PostStored>;
  readonly tags: EagerCollection<Tag_skip_id_, Tag_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly posts: EagerCollection<Post_skip_id_, PostStored>;
  readonly searchDocuments: EagerCollection<SearchSortKey, SearchDocument>;
  readonly searchDocumentsByPostId: EagerCollection<
    Post_skip_id_,
    SearchDocument
  >;
  readonly tags: EagerCollection<Tag_skip_id_, Tag_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_posts = inputs.posts;
  const searchDocuments = inputs.posts.map(
    ProjectSearchDocumentMapper,
    inputs.users,
    inputs.tags,
  );
  const output_searchDocuments = searchDocuments;
  const searchDocumentsByPostId = searchDocuments.map(SearchDocByPostIdMapper);
  const output_searchDocumentsByPostId = searchDocumentsByPostId;
  const output_tags = inputs.tags;
  const output_users = inputs.users;
  return {
    posts: output_posts,
    searchDocuments: output_searchDocuments,
    searchDocumentsByPostId: output_searchDocumentsByPostId,
    tags: output_tags,
    users: output_users,
  };
}
