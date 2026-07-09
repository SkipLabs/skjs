import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Post_skip_id_,
  PostStored,
  Post_skip_value_,
  CountAccum,
  Post,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each post entry, consult likeCountByPost for the values indexed by the entry's key (each consulted value is a CountAccum sum); if no values are consulted, treat the like count as zero, otherwise use the first consulted value. Consult commentCountByPost for the values indexed by the entry's key (each consulted value is a CountAccum sum); if no values are consulted, treat the comment count as zero, otherwise use the first consulted value. Emit one output pair whose key is the entry's key and whose value lists every required field of Post explicitly: authorId sourced from the entry's value's authorId field; content sourced from the entry's value's content field; createdAt sourced from the entry's value's createdAt field; likeCount sourced from the resolved like count; commentCount sourced from the resolved comment count. The optional updatedAt field is present when the entry's value's updatedAt field is present, sourced from the entry's value's updatedAt field; absent otherwise.
export class EnrichPostWithCountsMapper implements Mapper<
  Post_skip_id_,
  PostStored,
  Post_skip_id_,
  Post_skip_value_
> {
  constructor(
    private likeCountByPost: EagerCollection<Post_skip_id_, CountAccum>,
    private commentCountByPost: EagerCollection<Post_skip_id_, CountAccum>,
  ) {}

  mapEntry(
    key: Post_skip_id_,
    values: Values<PostStored>,
    context: Context,
  ): Iterable<[Post_skip_id_, Post_skip_value_]> {
    // > body
    for (const value of values.toArray()) {
      const likeValues = this.likeCountByPost.getArray(key);
      const likeCount = likeValues.length === 0 ? 0 : (likeValues[0] ?? 0);
      const commentValues = this.commentCountByPost.getArray(key);
      const commentCount =
        commentValues.length === 0 ? 0 : (commentValues[0] ?? 0);
      const out: Post_skip_value_ = {
        authorId: value.authorId,
        content: value.content,
        createdAt: value.createdAt,
        likeCount,
        commentCount,
        ...(value.updatedAt !== undefined && { updatedAt: value.updatedAt }),
      };
      return [[key, out]];
    }
    return [];
    // < body
  }
}
