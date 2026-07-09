import type { User_skip_id_, User_skip_value_, User } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetMeResourceInputs extends SharedCollections {
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export class GetMeResource implements Resource<GetMeResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetMeResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, User_skip_value_> {
    return inputs.users;
  }
}
