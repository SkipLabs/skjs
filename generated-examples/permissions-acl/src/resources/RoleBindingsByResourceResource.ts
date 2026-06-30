import type {
  ProtectedResource_skip_id_,
  RoleBindingByResourceValue,
  ProtectedResource,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface RoleBindingsByResourceResourceInputs extends SharedCollections {
  readonly roleBindingsByResource: EagerCollection<
    ProtectedResource_skip_id_,
    RoleBindingByResourceValue
  >;
}

export class RoleBindingsByResourceResource implements Resource<RoleBindingsByResourceResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: RoleBindingsByResourceResourceInputs,
    _context: Context,
  ): EagerCollection<ProtectedResource_skip_id_, RoleBindingByResourceValue> {
    return inputs.roleBindingsByResource;
  }
}
