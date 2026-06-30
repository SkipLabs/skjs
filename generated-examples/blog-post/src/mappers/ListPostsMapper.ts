import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Post_skip_id_, Post_skip_value_, Post } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each post entry, apply the filter predicate: (the status param is absent OR the entry's value's status field equals the status param) AND (the authorId param is absent OR the entry's value's authorId field equals the authorId param) AND (the tag param is absent OR the entry's value's tags array contains the tag param as a case-sensitive exact-match element). When the predicate holds, emit one output pair whose key is the entry's key and whose value lists every required field of Post explicitly: id sourced from the entry's key; authorId sourced from the entry's value's authorId field; title sourced from the entry's value's title field; content sourced from the entry's value's content field; status sourced from the entry's value's status field; tags sourced from the entry's value's tags field; createdAt sourced from the entry's value's createdAt field; updatedAt present when the entry's value's updatedAt field is present, sourced from the entry's value's updatedAt field, absent otherwise; publishedAt present when the entry's value's publishedAt field is present, sourced from the entry's value's publishedAt field, absent otherwise. Otherwise emit nothing.
export class ListPostsMapper implements Mapper<
  Post_skip_id_,
  Post_skip_value_,
  Post_skip_id_,
  Post
> {
  constructor(
    private status: string | null,
    private authorId: string | null,
    private tag: string | null,
  ) {}

  mapEntry(
    key: Post_skip_id_,
    values: Values<Post_skip_value_>,
    context: Context,
  ): Iterable<[Post_skip_id_, Post]> {
    // > body
    const value = values.toArray()[0];
    if (value === undefined) return [];
    if (this.status !== null && value.status !== this.status) return [];
    if (this.authorId !== null && value.authorId !== this.authorId) return [];
    if (this.tag !== null && !value.tags.includes(this.tag)) return [];
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
    return [[key, post]];
    // < body
  }
}
