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

// For each post entry, consult commentCountByPost for the value indexed by the entry's key; use the first consulted value as the comment count, defaulting to zero when the consultation yields nothing. Emit one output pair whose key is the entry's key and whose value lists every required field of Post_skip_value_ explicitly: authorId, title, body, status, tags, createdAt, updatedAt sourced from the entry's value; publishedAt is present when the entry's value's publishedAt field is present, sourced from that field, absent otherwise; commentCount is always present, sourced from the resolved comment count.
export class EnrichPostWithCommentCountMapper implements Mapper<
  Post_skip_id_,
  PostStored,
  Post_skip_id_,
  Post_skip_value_
> {
  constructor(
    private commentCountByPost: EagerCollection<Post_skip_id_, CommentCount>,
  ) {}

  mapEntry(
    key: Post_skip_id_,
    values: Values<PostStored>,
    context: Context,
  ): Iterable<[Post_skip_id_, Post_skip_value_]> {
    // > body
    const emits: [Post_skip_id_, Post_skip_value_][] = [];
    for (const value of values.toArray()) {
      const counts = this.commentCountByPost.getArray(key);
      const commentCount = counts[0] ?? 0;
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
