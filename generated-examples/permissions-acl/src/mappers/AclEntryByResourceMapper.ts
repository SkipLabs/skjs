import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  AclEntry_skip_id_,
  AclEntry_skip_value_,
  ResourceIdKey,
  AclEntry,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each acl-entry, emit one output pair whose key is sourced from the entry's key's resourceId field and whose value is an AclEntry record listing every required field explicitly: resourceId sourced from the entry's key's resourceId field (the original AclEntry.resourceId PK component is encoded into the new key AND preserved into the value's resourceId field); principalType sourced from the entry's key's principalType field (the original AclEntry.principalType PK component is preserved into the value's principalType field); principalId sourced from the entry's key's principalId field (the original AclEntry.principalId PK component is preserved into the value's principalId field); roleId sourced from the entry's key's roleId field (the original AclEntry.roleId PK component is preserved into the value's roleId field); grantedBy sourced from the entry's value's grantedBy field; grantedAt sourced from the entry's value's grantedAt field. All dropped key components are re-injected into the value so downstream consumers can reconstruct the full AclEntry.
export class AclEntryByResourceMapper implements Mapper<
  AclEntry_skip_id_,
  AclEntry_skip_value_,
  ResourceIdKey,
  AclEntry
> {
  mapEntry(
    key: AclEntry_skip_id_,
    values: Values<AclEntry_skip_value_>,
    context: Context,
  ): Iterable<[ResourceIdKey, AclEntry]> {
    // > body
    const emits: [ResourceIdKey, AclEntry][] = [];
    for (const value of values.toArray()) {
      const entry: AclEntry = {
        resourceId: key.resourceId,
        principalType: key.principalType,
        principalId: key.principalId,
        roleId: key.roleId,
        grantedBy: value.grantedBy,
        grantedAt: value.grantedAt,
      };
      emits.push([key.resourceId, entry]);
    }
    return emits;
    // < body
  }
}
