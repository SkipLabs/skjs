import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Binding_skip_id_,
  Binding_skip_value_,
  ApiKey_skip_id_,
  Binding,
  ApiKey,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each binding entry, emit one output pair whose key is sourced from the entry's value at the keyId field (a foreign key to ApiKey.id, hence typed as ApiKey_skip_id_), paired with a new value listing every required field of Binding explicitly: id sourced from the entry's key, ownerId sourced from the entry's value at the ownerId field, keyId sourced from the entry's value at the keyId field, policyId sourced from the entry's value at the policyId field, routePattern sourced from the entry's value at the routePattern field, and createdAt sourced from the entry's value at the createdAt field. This re-injects the original binding id (the input PK) on the value side so consumers can recover it from the re-keyed collection.
export class BindingByKeyIdMapper implements Mapper<
  Binding_skip_id_,
  Binding_skip_value_,
  ApiKey_skip_id_,
  Binding
> {
  mapEntry(
    key: Binding_skip_id_,
    values: Values<Binding_skip_value_>,
    context: Context,
  ): Iterable<[ApiKey_skip_id_, Binding]> {
    // > body
    const emits: [ApiKey_skip_id_, Binding][] = [];
    for (const value of values.toArray()) {
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
      emits.push([value.keyId, binding]);
    }
    return emits;
    // < body
  }
}
