import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Review_skip_id_,
  Review_skip_value_,
  User_skip_id_,
  Review,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each review entry, emit one output pair whose key is sourced from the entry's value authorId field (referencing User.id) and whose value lists every required field of Review explicitly: id sourced from the entry's key; subjectId sourced from the entry's value; authorId sourced from the entry's value; rating sourced from the entry's value; createdAt sourced from the entry's value; title present when the entry's value has a title field, sourced from the entry's value, absent otherwise; body present when the entry's value has a body field, sourced from the entry's value, absent otherwise; updatedAt present when the entry's value has an updatedAt field, sourced from the entry's value, absent otherwise. The original review id from the input key is re-injected into the output value's id field so consumers can reconstruct the full Review entity.
export class ReviewByAuthorPreservingIdMapper implements Mapper<
  Review_skip_id_,
  Review_skip_value_,
  User_skip_id_,
  Review
> {
  mapEntry(
    key: Review_skip_id_,
    values: Values<Review_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, Review]> {
    // > body
    const emits: [User_skip_id_, Review][] = [];
    for (const value of values.toArray()) {
      const review: Review = {
        id: key,
        subjectId: value.subjectId,
        authorId: value.authorId,
        rating: value.rating,
        createdAt: value.createdAt,
        ...(value.title !== undefined && { title: value.title }),
        ...(value.body !== undefined && { body: value.body }),
        ...(value.updatedAt !== undefined && { updatedAt: value.updatedAt }),
      };
      emits.push([value.authorId, review]);
    }
    return emits;
    // < body
  }
}
