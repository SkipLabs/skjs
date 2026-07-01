import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Comment_skip_id_,
  Comment_skip_value_,
  Post_skip_id_,
  Comment,
  Post,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each comment entry, emit one output pair whose key is sourced from the entry's value's postId field, and whose value lists every required field of Comment explicitly: id sourced from the entry's key (the comment id); postId sourced from the entry's value's postId field; authorId sourced from the entry's value's authorId field; content sourced from the entry's value's content field; createdAt sourced from the entry's value's createdAt field. Re-injecting the comment id on the value side is required so the api handler for GET /posts/{postId}/comments can emit full Comment objects (which require id) when consulting the re-keyed collection by postId. The original Comment.id is preserved in the value as id.
export class CommentByPostMapper implements Mapper<
  Comment_skip_id_,
  Comment_skip_value_,
  Post_skip_id_,
  Comment
> {
  mapEntry(
    key: Comment_skip_id_,
    values: Values<Comment_skip_value_>,
    context: Context,
  ): Iterable<[Post_skip_id_, Comment]> {
    // > body
    const emits: [Post_skip_id_, Comment][] = [];
    for (const value of values.toArray()) {
      const comment: Comment = {
        id: key,
        postId: value.postId,
        authorId: value.authorId,
        content: value.content,
        createdAt: value.createdAt,
      };
      emits.push([value.postId, comment]);
    }
    return emits;
    // < body
  }
}
