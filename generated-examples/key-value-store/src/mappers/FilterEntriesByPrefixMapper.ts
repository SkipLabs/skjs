import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  KvEntry_skip_id_,
  KvEntry_skip_value_,
  KvEntry,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry, when the prefix param is absent, emit the entry unchanged. When the prefix param is present, emit the entry unchanged if and only if the entry's key (a string) begins with the prefix param literally (character-by-character prefix match). Otherwise emit nothing.
export class FilterEntriesByPrefixMapper implements Mapper<
  KvEntry_skip_id_,
  KvEntry_skip_value_,
  KvEntry_skip_id_,
  KvEntry_skip_value_
> {
  constructor(private prefix: string | null) {}

  mapEntry(
    key: KvEntry_skip_id_,
    values: Values<KvEntry_skip_value_>,
    context: Context,
  ): Iterable<[KvEntry_skip_id_, KvEntry_skip_value_]> {
    // > body
    const emits: [KvEntry_skip_id_, KvEntry_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (this.prefix === null || key.startsWith(this.prefix)) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
