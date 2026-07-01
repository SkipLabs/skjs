import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  PostTagKey,
  PostTagStored,
  PostIdKey,
  PostTag,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry, emit a new key sourced from the entry's key's postId field, paired with a new value listing every required field of PostTag explicitly: postId sourced from the entry's key's postId, tagId sourced from the entry's key's tagId, createdAt sourced from the entry's value's createdAt. The original tagId from the entry's key is preserved in the value as tagId so the consumer can reconstruct the PostTag entity. The original postId from the entry's key is encoded into the new key.
export class PostTagByPostMapper implements Mapper<
  PostTagKey,
  PostTagStored,
  PostIdKey,
  PostTag
> {
  mapEntry(
    key: PostTagKey,
    values: Values<PostTagStored>,
    context: Context,
  ): Iterable<[PostIdKey, PostTag]> {
    // > body
    const emits: [PostIdKey, PostTag][] = [];
    for (const value of values.toArray()) {
      const postTag: PostTag = {
        postId: key.postId,
        tagId: key.tagId,
        createdAt: value.createdAt,
      };
      emits.push([key.postId, postTag]);
    }
    return emits;
    // < body
  }
}
