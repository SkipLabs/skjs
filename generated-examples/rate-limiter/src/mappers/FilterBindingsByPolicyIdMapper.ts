import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Policy_skip_id_, Binding, Policy } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry under the key: when the entry's key does not equal the policyId param, emit nothing. Otherwise iterate the values associated with the key and for each value in the values list, emit one output under the entry's key paired with the value unchanged. (The input collection accumulates all bindings for the same policyId under one key — the upstream BindingByPolicyIdMapper re-keys bindings from their natural PK to policyId, so multiple bindings can share the same key; singleton-only access would raise a non-unique-value error on any policyId with two or more bindings.)
export class FilterBindingsByPolicyIdMapper implements Mapper<
  Policy_skip_id_,
  Binding,
  Policy_skip_id_,
  Binding
> {
  constructor(private policyId: string) {}

  mapEntry(
    key: Policy_skip_id_,
    values: Values<Binding>,
    context: Context,
  ): Iterable<[Policy_skip_id_, Binding]> {
    // > body
    if (key !== this.policyId) return [];
    const emits: [Policy_skip_id_, Binding][] = [];
    for (const value of values.toArray()) {
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
