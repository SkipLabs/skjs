import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { LinkOwnerId, Link } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For the input key (an ownerId), when the entry's key does not equal the userId param, emit nothing. Otherwise iterate the values associated with the key and for each value, emit one output pair whose key is the entry's key and whose value is the value unchanged.
export class FilterLinksByOwnerIdMapper implements Mapper<
  LinkOwnerId,
  Link,
  LinkOwnerId,
  Link
> {
  constructor(private userId: string) {}

  mapEntry(
    key: LinkOwnerId,
    values: Values<Link>,
    context: Context,
  ): Iterable<[LinkOwnerId, Link]> {
    // > body
    if (key !== this.userId) return [];
    const emits: [LinkOwnerId, Link][] = [];
    for (const value of values) {
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
