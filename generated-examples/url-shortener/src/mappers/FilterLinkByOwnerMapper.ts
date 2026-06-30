import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Link_skip_id_, Link_skip_value_, Link } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each link entry, emit the entry unchanged when the entry's key equals the code param AND the entry's value ownerId field equals the userId param. Otherwise emit nothing.
export class FilterLinkByOwnerMapper implements Mapper<
  Link_skip_id_,
  Link_skip_value_,
  Link_skip_id_,
  Link_skip_value_
> {
  constructor(
    private code: string,
    private userId: string,
  ) {}

  mapEntry(
    key: Link_skip_id_,
    values: Values<Link_skip_value_>,
    context: Context,
  ): Iterable<[Link_skip_id_, Link_skip_value_]> {
    // > body
    const emits: [Link_skip_id_, Link_skip_value_][] = [];
    if (key !== this.code) return emits;
    for (const value of values.toArray()) {
      if (value.ownerId === this.userId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
