import type { Role_skip_id_, RoleBindingByRoleValue, Role } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface RoleBindingsByRoleResourceInputs extends SharedCollections {
  readonly roleBindingsByRole: EagerCollection<
    Role_skip_id_,
    RoleBindingByRoleValue
  >;
}

export class RoleBindingsByRoleResource implements Resource<RoleBindingsByRoleResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: RoleBindingsByRoleResourceInputs,
    _context: Context,
  ): EagerCollection<Role_skip_id_, RoleBindingByRoleValue> {
    return inputs.roleBindingsByRole;
  }
}
