import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { PostTagKey, PostTagStored, TagIdKey, PostTag } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry, emit a new key sourced from the entry's key's tagId field, paired with a new value listing every required field of PostTag explicitly: postId sourced from the entry's key's postId, tagId sourced from the entry's key's tagId, createdAt sourced from the entry's value's createdAt. The original postId from the entry's key is preserved in the value as postId so the consumer can reconstruct the PostTag entity. The original tagId from the entry's key is encoded into the new key.
export class PostTagByTagMapper implements Mapper<
  PostTagKey,
  PostTagStored,
  TagIdKey,
  PostTag
> {
  mapEntry(
    key: PostTagKey,
    values: Values<PostTagStored>,
    context: Context,
  ): Iterable<[TagIdKey, PostTag]> {
    // > body
    const emits: [TagIdKey, PostTag][] = [];
    for (const value of values.toArray()) {
      emits.push([
        key.tagId,
        {
          postId: key.postId,
          tagId: key.tagId,
          createdAt: value.createdAt,
        },
      ]);
    }
    return emits;
    // < body
  }
}
