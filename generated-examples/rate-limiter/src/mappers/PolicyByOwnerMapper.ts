import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Policy_skip_id_, Policy_skip_value_, Policy } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each policy entry, emit the entry unchanged (keyed by its original policy id) when the entry's ownerId field equals the userId param. Otherwise emit nothing.
export class PolicyByOwnerMapper implements Mapper<
  Policy_skip_id_,
  Policy_skip_value_,
  Policy_skip_id_,
  Policy_skip_value_
> {
  constructor(private userId: string) {}

  mapEntry(
    key: Policy_skip_id_,
    values: Values<Policy_skip_value_>,
    context: Context,
  ): Iterable<[Policy_skip_id_, Policy_skip_value_]> {
    // > body
    const emits: [Policy_skip_id_, Policy_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (value.ownerId === this.userId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
