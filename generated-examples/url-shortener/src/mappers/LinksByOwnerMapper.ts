import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Link_skip_id_,
  Link_skip_value_,
  LinkOwnerId,
  Link,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each link entry, emit one output pair whose key is sourced from the entry's value ownerId field, paired with a new value listing every required field of Link explicitly: code is sourced from the entry's key; targetUrl is sourced from the entry's value targetUrl field; ownerId is sourced from the entry's value ownerId field; clickCount is sourced from the entry's value clickCount field; createdAt is sourced from the entry's value createdAt field; description is sourced from the entry's value description field.
export class LinksByOwnerMapper implements Mapper<
  Link_skip_id_,
  Link_skip_value_,
  LinkOwnerId,
  Link
> {
  mapEntry(
    key: Link_skip_id_,
    values: Values<Link_skip_value_>,
    context: Context,
  ): Iterable<[LinkOwnerId, Link]> {
    // > body
    const emits: [LinkOwnerId, Link][] = [];
    for (const value of values.toArray()) {
      const link: Link = {
        code: key,
        targetUrl: value.targetUrl,
        ownerId: value.ownerId,
        clickCount: value.clickCount,
        createdAt: value.createdAt,
        ...(value.description !== undefined && {
          description: value.description,
        }),
      };
      emits.push([value.ownerId, link]);
    }
    return emits;
    // < body
  }
}
