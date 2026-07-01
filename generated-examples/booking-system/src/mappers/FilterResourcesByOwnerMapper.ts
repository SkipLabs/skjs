import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  BookableResource_skip_id_,
  BookableResource_skip_value_,
  BookableResource,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each resource entry, when the ownerId param is absent, emit the entry unchanged. When the ownerId param is present, emit the entry unchanged if and only if the entry's value's ownerId field equals the ownerId param. Otherwise emit nothing.
export class FilterResourcesByOwnerMapper implements Mapper<
  BookableResource_skip_id_,
  BookableResource_skip_value_,
  BookableResource_skip_id_,
  BookableResource_skip_value_
> {
  constructor(private ownerId: string | null) {}

  mapEntry(
    key: BookableResource_skip_id_,
    values: Values<BookableResource_skip_value_>,
    context: Context,
  ): Iterable<[BookableResource_skip_id_, BookableResource_skip_value_]> {
    // > body
    const emits: [BookableResource_skip_id_, BookableResource_skip_value_][] =
      [];
    for (const value of values.toArray()) {
      if (this.ownerId === null || value.ownerId === this.ownerId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
