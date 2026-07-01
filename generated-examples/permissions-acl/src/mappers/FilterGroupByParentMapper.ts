import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Group_skip_id_, Group_skip_value_, Group } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each group entry, when the parentGroupId param is absent, emit the entry unchanged. Otherwise emit the entry unchanged when the entry's value parentGroupId field equals the parentGroupId param; emit nothing otherwise.
export class FilterGroupByParentMapper implements Mapper<
  Group_skip_id_,
  Group_skip_value_,
  Group_skip_id_,
  Group_skip_value_
> {
  constructor(private parentGroupId: string | null) {}

  mapEntry(
    key: Group_skip_id_,
    values: Values<Group_skip_value_>,
    context: Context,
  ): Iterable<[Group_skip_id_, Group_skip_value_]> {
    // > body
    const emits: [Group_skip_id_, Group_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (this.parentGroupId === null) {
        emits.push([key, value]);
      } else if (value.parentGroupId === this.parentGroupId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
