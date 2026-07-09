import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Post_skip_id_,
  PostStored,
  SearchDocument,
  User_skip_id_,
  User_skip_value_,
  PostIdKey,
  PostTag,
  Tag_skip_id_,
  Tag_skip_value_,
  Post,
  User,
  Tag,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each post entry: (1) consult users for the values indexed by the entry's value's authorId to obtain the author's user value; if empty, treat authorDisplayName and authorUsername as the empty string; otherwise use the first user value and take its displayName field (defaulted to the empty string when absent) as authorDisplayName and its username field (defaulted to the empty string when absent) as authorUsername. (2) consult postTagsByPost for the PostTag values indexed by the entry's key; for each consulted PostTag, consult tags for the values indexed by the PostTag's tagId; if empty skip, otherwise take the first tag value's name field. Collect all such names into an array and sort ascending lexicographic on the name string value. (3) compute searchText as the concatenation of [entry's value's title, entry's value's body, authorDisplayName, authorUsername, ...sortedTagNames] joined with single spaces, then lower-cased. (4) emit one output pair whose key is the entry's key and whose value lists every required field of SearchDocument explicitly: postId sourced from the entry's key, authorId sourced from the entry's value's authorId, title sourced from the entry's value's title, body sourced from the entry's value's body, tagNames sourced from the sorted tag names array, searchText sourced from the computed searchText, createdAt sourced from the entry's value's createdAt. Optional fields: authorDisplayName is always present, sourced from the resolved authorDisplayName; authorUsername is always present, sourced from the resolved authorUsername; updatedAt is present when the entry's value's updatedAt is present, sourced from the entry's value's updatedAt; absent otherwise.
export class AssembleSearchDocumentMapper implements Mapper<
  Post_skip_id_,
  PostStored,
  Post_skip_id_,
  SearchDocument
> {
  constructor(
    private users: EagerCollection<User_skip_id_, User_skip_value_>,
    private postTagsByPost: EagerCollection<PostIdKey, PostTag>,
    private tags: EagerCollection<Tag_skip_id_, Tag_skip_value_>,
  ) {}

  mapEntry(
    key: Post_skip_id_,
    values: Values<PostStored>,
    context: Context,
  ): Iterable<[Post_skip_id_, SearchDocument]> {
    // > body
    const emits: [Post_skip_id_, SearchDocument][] = [];
    for (const value of values.toArray()) {
      const userValues = this.users.getArray(value.authorId);
      let authorDisplayName = "";
      let authorUsername = "";
      const firstUser = userValues[0];
      if (firstUser !== undefined) {
        authorDisplayName = firstUser.displayName ?? "";
        authorUsername = firstUser.username ?? "";
      }

      const postTags = this.postTagsByPost.getArray(key);
      const tagNames: string[] = [];
      for (const pt of postTags) {
        const tagValues = this.tags.getArray(pt.tagId);
        const firstTag = tagValues[0];
        if (firstTag === undefined) continue;
        tagNames.push(firstTag.name);
      }
      tagNames.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));

      const searchText = [
        value.title,
        value.body,
        authorDisplayName,
        authorUsername,
        ...tagNames,
      ]
        .join(" ")
        .toLowerCase();

      const doc: SearchDocument = {
        postId: key,
        authorId: value.authorId,
        title: value.title,
        body: value.body,
        tagNames,
        searchText,
        createdAt: value.createdAt,
        authorDisplayName,
        authorUsername,
        ...(value.updatedAt !== undefined && { updatedAt: value.updatedAt }),
      };
      emits.push([key, doc]);
    }
    return emits;
    // < body
  }
}
