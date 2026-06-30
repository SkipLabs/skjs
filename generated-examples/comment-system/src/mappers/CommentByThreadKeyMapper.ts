import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Comment_skip_id_,
  CommentStored,
  ThreadKey,
  Comment,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each comment entry, emit one output pair whose key is sourced from the entry's threadKey field and whose value is the entry's key (the comment id). The original comment id from from[0] is preserved in the output value so a downstream join mapper can re-fetch the full Comment by id from inputs.comments. The original threadKey from from[1] is encoded into the new key. All other fields of from[1] are dropped because they are recovered by the downstream join mapper from inputs.comments.
export class CommentByThreadKeyMapper implements Mapper<
  Comment_skip_id_,
  CommentStored,
  ThreadKey,
  Comment_skip_id_
> {
  mapEntry(
    key: Comment_skip_id_,
    values: Values<CommentStored>,
    context: Context,
  ): Iterable<[ThreadKey, Comment_skip_id_]> {
    // > body
    const emits: [ThreadKey, Comment_skip_id_][] = [];
    for (const value of values.toArray()) {
      emits.push([value.threadKey, key]);
    }
    return emits;
    // < body
  }
}
