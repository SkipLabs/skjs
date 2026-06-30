import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Post_skip_id_, Post_skip_value_, Post } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each post entry, emit one output pair whose key is the entry's key and whose value lists every required field of Post explicitly: id sourced from the entry's key; authorId sourced from the entry's value's authorId field; title sourced from the entry's value's title field; content sourced from the entry's value's content field; status sourced from the entry's value's status field; tags sourced from the entry's value's tags field; createdAt sourced from the entry's value's createdAt field; updatedAt present when the entry's value's updatedAt field is present, sourced from the entry's value's updatedAt field, absent otherwise; publishedAt present when the entry's value's publishedAt field is present, sourced from the entry's value's publishedAt field, absent otherwise.
export class AssemblePostMapper implements Mapper<
  Post_skip_id_,
  Post_skip_value_,
  Post_skip_id_,
  Post
> {
  mapEntry(
    key: Post_skip_id_,
    values: Values<Post_skip_value_>,
    context: Context,
  ): Iterable<[Post_skip_id_, Post]> {
    // > body
    const emits: [Post_skip_id_, Post][] = [];
    for (const value of values.toArray()) {
      const post: Post = {
        id: key,
        authorId: value.authorId,
        title: value.title,
        content: value.content,
        status: value.status,
        tags: value.tags,
        createdAt: value.createdAt,
        ...(value.updatedAt !== undefined && { updatedAt: value.updatedAt }),
        ...(value.publishedAt !== undefined && {
          publishedAt: value.publishedAt,
        }),
      };
      emits.push([key, post]);
    }
    return emits;
    // < body
  }
}
