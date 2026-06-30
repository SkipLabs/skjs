import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Poll_skip_id_, Poll_skip_value_, Poll } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each poll entry, emit the entry unchanged when the ownerId param is absent. Otherwise emit the entry unchanged when the entry's value's ownerId field equals the ownerId param; emit nothing otherwise.
export class FilterPollsByOwnerMapper implements Mapper<
  Poll_skip_id_,
  Poll_skip_value_,
  Poll_skip_id_,
  Poll_skip_value_
> {
  constructor(private ownerId: string | null) {}

  mapEntry(
    key: Poll_skip_id_,
    values: Values<Poll_skip_value_>,
    context: Context,
  ): Iterable<[Poll_skip_id_, Poll_skip_value_]> {
    // > body
    const emits: [Poll_skip_id_, Poll_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (this.ownerId === null || value.ownerId === this.ownerId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
