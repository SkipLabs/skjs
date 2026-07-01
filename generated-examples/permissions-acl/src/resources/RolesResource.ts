import type { Role_skip_id_, Role_skip_value_, Role } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface RolesResourceInputs extends SharedCollections {
  readonly roles: EagerCollection<Role_skip_id_, Role_skip_value_>;
}

export class RolesResource implements Resource<RolesResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: RolesResourceInputs,
    _context: Context,
  ): EagerCollection<Role_skip_id_, Role_skip_value_> {
    return inputs.roles;
  }
}
