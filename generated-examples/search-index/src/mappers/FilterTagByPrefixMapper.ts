import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Tag_skip_id_,
  Tag_skip_value_,
  TagNameSortKey,
  Tag,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each tag entry, when the namePrefix param is present AND the entry's name field (lowercased) does not begin with the namePrefix param (lowercased), emit nothing. Otherwise emit one output pair whose key is a composite carrying name sourced from the entry's name field (lowercased) and id sourced from the entry's key, paired with the entry's value unchanged. The composite key sorts ascending by name then by id.
export class FilterTagByPrefixMapper implements Mapper<
  Tag_skip_id_,
  Tag_skip_value_,
  TagNameSortKey,
  Tag_skip_value_
> {
  constructor(private namePrefix: string | null) {}

  mapEntry(
    key: Tag_skip_id_,
    values: Values<Tag_skip_value_>,
    context: Context,
  ): Iterable<[TagNameSortKey, Tag_skip_value_]> {
    // > body
    if (this.namePrefix !== null) {
      const prefix = this.namePrefix.toLowerCase();
      const emits: [TagNameSortKey, Tag_skip_value_][] = [];
      for (const value of values.toArray()) {
        const lowerName = value.name.toLowerCase();
        if (!lowerName.startsWith(prefix)) continue;
        emits.push([{ name: lowerName, id: key }, value]);
      }
      return emits;
    }
    const emits: [TagNameSortKey, Tag_skip_value_][] = [];
    for (const value of values.toArray()) {
      emits.push([{ name: value.name.toLowerCase(), id: key }, value]);
    }
    return emits;
    // < body
  }
}
