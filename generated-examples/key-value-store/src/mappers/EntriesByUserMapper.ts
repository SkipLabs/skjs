import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  KvEntry_skip_id_,
  KvEntry_skip_value_,
  UserId,
  EntriesByUserMapperOut,
  KvEntry,
} from "../types.js";
import type { Json, Context, Mapper, Values } from "@skipruntime/core";

// For each kv entry, emit one output pair whose key is sourced from the entry's key's userId field and whose value lists every required field of EntriesByUserMapperOut explicitly: userId sourced from the entry's key's userId field, key sourced from the entry's key's key field, value sourced from the entry's value's value field, createdAt sourced from the entry's value's createdAt field, updatedAt sourced from the entry's value's updatedAt field, revision sourced from the entry's value's revision field.
export class EntriesByUserMapper implements Mapper<
  KvEntry_skip_id_,
  KvEntry_skip_value_,
  UserId,
  EntriesByUserMapperOut
> {
  mapEntry(
    key: KvEntry_skip_id_,
    values: Values<KvEntry_skip_value_>,
    context: Context,
  ): Iterable<[UserId, EntriesByUserMapperOut]> {
    // > body
    const emits: [UserId, EntriesByUserMapperOut][] = [];
    for (const value of values.toArray()) {
      const out: EntriesByUserMapperOut = {
        userId: key.userId,
        key: key.key,
        value: (() => {
          const v = value.value;
          if (isJsonObject(v)) {
            const obj: Record<string, Json> = {};
            for (const k of Object.keys(v)) {
              const item = v[k];
              if (item !== undefined && item !== null) obj[k] = item;
              else if (item === null) obj[k] = null;
            }
            return obj;
          }
          return {};
        })(),
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
        revision: value.revision,
      };
      emits.push([key.userId, out]);
    }
    return emits;
    // < body
  }
}
