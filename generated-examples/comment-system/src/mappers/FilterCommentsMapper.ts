import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Comment_skip_id_,
  Comment_skip_value_,
  Comment,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry, apply each optional filter in sequence. If the parentCommentId param is present, emit nothing when the entry's value's parentCommentId field is absent or does not equal the param. If the rootOnly param is present and equals true, emit nothing when the entry's value carries a parentCommentId field. If the authorId param is present, emit nothing when the entry's value's authorId field does not equal the param. Otherwise emit the entry unchanged.
export class FilterCommentsMapper implements Mapper<
  Comment_skip_id_,
  Comment_skip_value_,
  Comment_skip_id_,
  Comment_skip_value_
> {
  constructor(
    private parentCommentId: string | null,
    private rootOnly: boolean | null,
    private authorId: string | null,
  ) {}

  mapEntry(
    key: Comment_skip_id_,
    values: Values<Comment_skip_value_>,
    context: Context,
  ): Iterable<[Comment_skip_id_, Comment_skip_value_]> {
    // > body
    const emits: [Comment_skip_id_, Comment_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (this.parentCommentId !== null) {
        if (
          value.parentCommentId === undefined ||
          value.parentCommentId !== this.parentCommentId
        ) {
          continue;
        }
      }
      if (this.rootOnly !== null && this.rootOnly === true) {
        if (value.parentCommentId !== undefined) {
          continue;
        }
      }
      if (this.authorId !== null) {
        if (value.authorId !== this.authorId) {
          continue;
        }
      }
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
