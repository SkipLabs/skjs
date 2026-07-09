import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  KvEntry_skip_id_,
  KvEntry_skip_value_,
  KvEntry,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each kv entry, emit the entry unchanged when the entry's key's userId field equals the userId param AND the entry's key's key field equals the key param. Otherwise emit nothing.
export class FilterEntryByUserAndKeyMapper implements Mapper<
  KvEntry_skip_id_,
  KvEntry_skip_value_,
  KvEntry_skip_id_,
  KvEntry_skip_value_
> {
  constructor(
    private userId: string,
    private key: string,
  ) {}

  mapEntry(
    key: KvEntry_skip_id_,
    values: Values<KvEntry_skip_value_>,
    context: Context,
  ): Iterable<[KvEntry_skip_id_, KvEntry_skip_value_]> {
    // > body
    if (key.userId !== this.userId || key.key !== this.key) return [];
    const emits: [KvEntry_skip_id_, KvEntry_skip_value_][] = [];
    for (const value of values.toArray()) {
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
