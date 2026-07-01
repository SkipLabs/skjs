import type { Role_skip_id_, Role_skip_value_, Role } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetRoleResourceInputs extends SharedCollections {
  readonly roles: EagerCollection<Role_skip_id_, Role_skip_value_>;
}

export class GetRoleResource implements Resource<GetRoleResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetRoleResourceInputs,
    _context: Context,
  ): EagerCollection<Role_skip_id_, Role_skip_value_> {
    return inputs.roles;
  }
}
