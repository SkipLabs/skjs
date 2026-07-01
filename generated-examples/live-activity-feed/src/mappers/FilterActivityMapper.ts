import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { ActivityCreatedAtKey, Activity } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry under the negated-epoch numeric key, iterate the values associated with the key and for each value, when ((the authorId param is absent) OR (the value's authorId field equals the authorId param)) AND ((the type param is absent) OR (the value's type field equals the type param)), emit one output under the same key paired with that value; otherwise emit nothing for that value. (The upstream re-key by negated-epoch can accumulate multiple activities under one key when two activities share the same createdAt; iteration is required — singleton-only access would raise on any timestamp collision.)
export class FilterActivityMapper implements Mapper<
  ActivityCreatedAtKey,
  Activity,
  ActivityCreatedAtKey,
  Activity
> {
  constructor(
    private authorId: string | null,
    private type: string | null,
  ) {}

  mapEntry(
    key: ActivityCreatedAtKey,
    values: Values<Activity>,
    context: Context,
  ): Iterable<[ActivityCreatedAtKey, Activity]> {
    // > body
    const emits: [ActivityCreatedAtKey, Activity][] = [];
    for (const value of values.toArray()) {
      if (
        (this.authorId === null || value.authorId === this.authorId) &&
        (this.type === null || value.type === this.type)
      ) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
