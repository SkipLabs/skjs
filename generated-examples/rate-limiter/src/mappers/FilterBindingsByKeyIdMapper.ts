import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { ApiKey_skip_id_, Binding, ApiKey } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry under the key: when the entry's key does not equal the keyId param, emit nothing. Otherwise iterate the values associated with the key and for each value in the values list, emit one output under the entry's key paired with the value unchanged. (The input collection accumulates all bindings for the same keyId under one key — the upstream BindingByKeyIdMapper re-keys bindings from their natural PK to keyId, so multiple bindings can share the same key; singleton-only access would raise a non-unique-value error on any keyId with two or more bindings.)
export class FilterBindingsByKeyIdMapper implements Mapper<
  ApiKey_skip_id_,
  Binding,
  ApiKey_skip_id_,
  Binding
> {
  constructor(private keyId: string) {}

  mapEntry(
    key: ApiKey_skip_id_,
    values: Values<Binding>,
    context: Context,
  ): Iterable<[ApiKey_skip_id_, Binding]> {
    // > body
    if (key !== this.keyId) return [];
    const emits: [ApiKey_skip_id_, Binding][] = [];
    for (const value of values.toArray()) {
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
