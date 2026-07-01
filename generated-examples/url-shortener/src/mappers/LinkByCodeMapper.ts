import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Link_skip_id_,
  Link_skip_value_,
  LinkShortCode,
  Link,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each link entry, emit one output pair whose key is sourced from the entry's value at the code field (an opaque short-code string) and whose value is a new Link object listing every required field explicitly: id sourced from the entry's key, ownerId/code/targetUrl/clickCount/createdAt sourced from the entry's value. This re-injects the link id on the value side so resolveShortCode can consult by code and directly obtain the id for the clickCount increment write.
export class LinkByCodeMapper implements Mapper<
  Link_skip_id_,
  Link_skip_value_,
  LinkShortCode,
  Link
> {
  mapEntry(
    key: Link_skip_id_,
    values: Values<Link_skip_value_>,
    context: Context,
  ): Iterable<[LinkShortCode, Link]> {
    // > body
    const emits: [LinkShortCode, Link][] = [];
    for (const value of values.toArray()) {
      const link: Link = {
        id: key,
        ownerId: value.ownerId,
        code: value.code,
        targetUrl: value.targetUrl,
        clickCount: value.clickCount,
        createdAt: value.createdAt,
      };
      emits.push([value.code, link]);
    }
    return emits;
    // < body
  }
}
