import type { User_skip_id_, User_skip_value_, User } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface getMeResourceInputs extends SharedCollections {
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export class getMeResource implements Resource<getMeResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: getMeResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, User_skip_value_> {
    return inputs.users;
  }
}
