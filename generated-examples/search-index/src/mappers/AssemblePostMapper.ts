import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Post_skip_id_,
  PostStored,
  Post_skip_value_,
  PostIdKey,
  PostTag,
  Post,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each entry, consult postTagsByPost for the PostTag values indexed by the entry's key. Collect the tagId field from each consulted PostTag value into an array, then sort that array ascending lexicographic on the tagId string value. Emit one output pair whose key is the entry's key and whose value lists every required field of Post explicitly: id sourced from the entry's key, authorId sourced from the entry's value's authorId, title sourced from the entry's value's title, body sourced from the entry's value's body, createdAt sourced from the entry's value's createdAt. Optional fields: updatedAt is present when the entry's value's updatedAt is present, sourced from the entry's value's updatedAt; absent otherwise. tagIds is always present, sourced from the sorted tagId array (empty array when no PostTag values were consulted).
export class AssemblePostMapper implements Mapper<
  Post_skip_id_,
  PostStored,
  Post_skip_id_,
  Post_skip_value_
> {
  constructor(private postTagsByPost: EagerCollection<PostIdKey, PostTag>) {}

  mapEntry(
    key: Post_skip_id_,
    values: Values<PostStored>,
    context: Context,
  ): Iterable<[Post_skip_id_, Post_skip_value_]> {
    // > body
    const emits: [Post_skip_id_, Post_skip_value_][] = [];
    for (const value of values.toArray()) {
      const postTags = this.postTagsByPost.getArray(key);
      const tagIds: string[] = [];
      for (const pt of postTags) {
        tagIds.push(pt.tagId);
      }
      tagIds.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
      const out: Post_skip_value_ = {
        authorId: value.authorId,
        title: value.title,
        body: value.body,
        createdAt: value.createdAt,
        ...(value.updatedAt !== undefined && { updatedAt: value.updatedAt }),
        tagIds,
      };
      emits.push([key, out]);
    }
    return emits;
    // < body
  }
}
