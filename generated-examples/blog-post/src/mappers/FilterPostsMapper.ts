import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Post_skip_id_,
  PostStored,
  Post_skip_value_,
  CommentCount,
  Post,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each post entry, apply the following filters in sequence: (a) when the authorId param is present, keep the entry only when its value's authorId field equals the authorId param; (b) when the status param is present, keep the entry only when its value's status field equals the status param; (c) when the tag param is present, keep the entry only when its value's tags array contains the tag param as one of its string elements. When all applicable filters pass, consult commentCountByPost for the value indexed by the entry's key; use the first consulted value as the comment count, defaulting to zero when the consultation yields nothing. Emit one output pair whose key is the entry's key and whose value lists every required field of Post_skip_value_ explicitly: authorId, title, body, status, tags, createdAt, updatedAt sourced from the entry's value; publishedAt is present when the entry's value's publishedAt field is present, sourced from that field, absent otherwise; commentCount is always present, sourced from the resolved comment count. Otherwise emit nothing.
export class FilterPostsMapper implements Mapper<
  Post_skip_id_,
  PostStored,
  Post_skip_id_,
  Post_skip_value_
> {
  constructor(
    private commentCountByPost: EagerCollection<Post_skip_id_, CommentCount>,
    private authorId: string | null,
    private status: string | null,
    private tag: string | null,
  ) {}

  mapEntry(
    key: Post_skip_id_,
    values: Values<PostStored>,
    context: Context,
  ): Iterable<[Post_skip_id_, Post_skip_value_]> {
    // > body
    const emits: [Post_skip_id_, Post_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (this.authorId !== null && value.authorId !== this.authorId) continue;
      if (this.status !== null && value.status !== this.status) continue;
      if (this.tag !== null && !value.tags.includes(this.tag)) continue;
      const counts = this.commentCountByPost.getArray(key);
      const first = counts[0];
      const commentCount = first === undefined ? 0 : first;
      const out: Post_skip_value_ = {
        authorId: value.authorId,
        title: value.title,
        body: value.body,
        status: value.status,
        tags: value.tags,
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
        ...(value.publishedAt !== undefined && {
          publishedAt: value.publishedAt,
        }),
        commentCount,
      };
      emits.push([key, out]);
    }
    return emits;
    // < body
  }
}
