import type {
  RoleBinding_skip_id_,
  RoleBinding_skip_value_,
  RoleBinding,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetRoleBindingResourceInputs extends SharedCollections {
  readonly roleBindings: EagerCollection<
    RoleBinding_skip_id_,
    RoleBinding_skip_value_
  >;
}

export class GetRoleBindingResource implements Resource<GetRoleBindingResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetRoleBindingResourceInputs,
    _context: Context,
  ): EagerCollection<RoleBinding_skip_id_, RoleBinding_skip_value_> {
    return inputs.roleBindings;
  }
}
