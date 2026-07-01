import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Post_skip_id_,
  PostStored,
  SearchSortKey,
  SearchDocument,
  User_skip_id_,
  User_skip_value_,
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

// For each post entry, project the denormalised SearchDocument. Consult users for the values indexed by the entry's authorId field; when the consultation yields at least one value, use the first; otherwise treat the author as absent for username/displayName denormalisation. Consult tags for each tagId in the entry's tagIds array, in order; when a consultation yields at least one value, take its name field; when none, skip that id from tagNames (the tag was deleted and the source post's tagIds array is being kept in sync separately). Emit one output pair whose key is a composite carrying createdAtNeg (the entry's createdAt parsed to epoch milliseconds and negated, so ascending sort yields descending createdAt) and postId sourced from the entry's key, paired with a SearchDocument value listing every REQUIRED field of SearchDocument explicitly: postId sourced from the entry's key; authorId sourced from the entry's authorId field; title sourced from the entry's title field; body sourced from the entry's body field; tagIds sourced from the entry's tagIds field; tagNames built from the resolved tag-name list per the consultation above; createdAt sourced from the entry's createdAt field; updatedAt sourced from the entry's updatedAt field. OPTIONAL fields: authorUsername present when the consulted author value's username field is present, sourced from that field; absent otherwise. authorDisplayName present when the consulted author value's displayName field is present, sourced from that field; absent otherwise.
export class ProjectSearchDocumentMapper implements Mapper<
  Post_skip_id_,
  PostStored,
  SearchSortKey,
  SearchDocument
> {
  constructor(
    private users: EagerCollection<User_skip_id_, User_skip_value_>,
    private tags: EagerCollection<Tag_skip_id_, Tag_skip_value_>,
  ) {}

  mapEntry(
    key: Post_skip_id_,
    values: Values<PostStored>,
    context: Context,
  ): Iterable<[SearchSortKey, SearchDocument]> {
    // > body
    const emits: [SearchSortKey, SearchDocument][] = [];
    for (const value of values.toArray()) {
      const authorValues = this.users.getArray(value.authorId);
      const author = authorValues[0];

      const tagNames: string[] = [];
      for (const tagId of value.tagIds) {
        const tagValues = this.tags.getArray(tagId);
        const tag = tagValues[0];
        if (tag === undefined) continue;
        tagNames.push(tag.name);
      }

      const createdAtNeg = -new Date(value.createdAt).getTime();
      const sortKey: SearchSortKey = { createdAtNeg, postId: key };

      const doc: SearchDocument = {
        postId: key,
        authorId: value.authorId,
        title: value.title,
        body: value.body,
        tagIds: value.tagIds,
        tagNames,
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
        ...(author !== undefined &&
          author.username !== undefined && { authorUsername: author.username }),
        ...(author !== undefined &&
          author.displayName !== undefined && {
            authorDisplayName: author.displayName,
          }),
      };

      emits.push([sortKey, doc]);
    }
    return emits;
    // < body
  }
}
