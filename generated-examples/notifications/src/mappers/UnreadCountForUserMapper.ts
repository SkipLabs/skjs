import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  RecipientUserId,
  UnreadCountAccum,
  UnreadCount,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry, when the entry's key does not equal the userId param, emit nothing. Otherwise emit one output pair whose key is the literal-zero and whose value lists every required field of UnreadCount explicitly: count sourced from the entry's value. On an empty source for the userId param, the output is empty by reactive construction — the consumer api method handles the zero-default by projecting an absent result to a count of zero.
export class UnreadCountForUserMapper implements Mapper<
  RecipientUserId,
  UnreadCountAccum,
  0,
  UnreadCount
> {
  constructor(private userId: string) {}

  mapEntry(
    key: RecipientUserId,
    values: Values<UnreadCountAccum>,
    context: Context,
  ): Iterable<[0, UnreadCount]> {
    // > body
    if (key !== this.userId) return [];
    let count = 0;
    for (const value of values.toArray()) count += value;
    return [[0, { count }]];
    // < body
  }
}
