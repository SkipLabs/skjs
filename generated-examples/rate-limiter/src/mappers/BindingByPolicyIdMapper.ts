import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Binding_skip_id_,
  Binding_skip_value_,
  Policy_skip_id_,
  Binding,
  Policy,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each binding entry, emit one output pair whose key is sourced from the entry's value at the policyId field (a foreign key to Policy.id, hence typed as Policy_skip_id_), paired with a new value listing every required field of Binding explicitly: id sourced from the entry's key, ownerId sourced from the entry's value at the ownerId field, keyId sourced from the entry's value at the keyId field, policyId sourced from the entry's value at the policyId field, routePattern sourced from the entry's value at the routePattern field, and createdAt sourced from the entry's value at the createdAt field. Produces an index used by deletePolicy to enumerate the bindings referencing the deleted policy for cascade cleanup.
export class BindingByPolicyIdMapper implements Mapper<
  Binding_skip_id_,
  Binding_skip_value_,
  Policy_skip_id_,
  Binding
> {
  mapEntry(
    key: Binding_skip_id_,
    values: Values<Binding_skip_value_>,
    context: Context,
  ): Iterable<[Policy_skip_id_, Binding]> {
    // > body
    const emits: [Policy_skip_id_, Binding][] = [];
    for (const value of values) {
      const binding: Binding = {
        id: key,
        ownerId: value.ownerId,
        keyId: value.keyId,
        policyId: value.policyId,
        createdAt: value.createdAt,
        ...(value.routePattern !== undefined && {
          routePattern: value.routePattern,
        }),
      };
      emits.push([value.policyId, binding]);
    }
    return emits;
    // < body
  }
}
