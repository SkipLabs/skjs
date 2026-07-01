import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { LeaderboardSortKey, UserAggregate } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry, emit one output pair whose key is the literal zero and whose value is the entry's value unchanged. This shuffles ALL entries under a single constant key so a downstream mapper can iterate them together in sorted order. The original LeaderboardSortKey components are preserved via the value's totalPoints, lastSubmittedAtMs, and userId fields, so the downstream sorter can reconstruct the ordering.
export class ShuffleAllToZeroMapper implements Mapper<
  LeaderboardSortKey,
  UserAggregate,
  0,
  UserAggregate
> {
  mapEntry(
    key: LeaderboardSortKey,
    values: Values<UserAggregate>,
    context: Context,
  ): Iterable<[0, UserAggregate]> {
    // > body
    const emits: [0, UserAggregate][] = [];
    for (const value of values.toArray()) {
      emits.push([0, value]);
    }
    return emits;
    // < body
  }
}
