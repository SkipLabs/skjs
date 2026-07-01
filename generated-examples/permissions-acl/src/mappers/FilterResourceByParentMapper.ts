import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ProtectedResource_skip_id_,
  ProtectedResource_skip_value_,
  ProtectedResource,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each resource entry, when the parentResourceId param is absent, emit the entry unchanged. Otherwise emit the entry unchanged when the entry's value parentResourceId field equals the parentResourceId param; emit nothing otherwise.
export class FilterResourceByParentMapper implements Mapper<
  ProtectedResource_skip_id_,
  ProtectedResource_skip_value_,
  ProtectedResource_skip_id_,
  ProtectedResource_skip_value_
> {
  constructor(private parentResourceId: string | null) {}

  mapEntry(
    key: ProtectedResource_skip_id_,
    values: Values<ProtectedResource_skip_value_>,
    context: Context,
  ): Iterable<[ProtectedResource_skip_id_, ProtectedResource_skip_value_]> {
    // > body
    const emits: [ProtectedResource_skip_id_, ProtectedResource_skip_value_][] =
      [];
    for (const value of values.toArray()) {
      if (
        this.parentResourceId === null ||
        this.parentResourceId === undefined
      ) {
        emits.push([key, value]);
      } else if (value.parentResourceId === this.parentResourceId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
