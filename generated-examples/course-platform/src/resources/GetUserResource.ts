import type { User_skip_id_, User_skip_value_, User } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetUserResourceInputs extends SharedCollections {
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export class GetUserResource implements Resource<GetUserResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetUserResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, User_skip_value_> {
    return inputs.users;
  }
}
