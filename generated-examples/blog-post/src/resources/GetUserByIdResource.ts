import { AssembleUserMapper } from "../mappers/AssembleUserMapper.js";
import type { User_skip_id_, User_skip_value_, User } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetUserByIdResourceInputs extends SharedCollections {
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export class GetUserByIdResource implements Resource<GetUserByIdResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetUserByIdResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, User> {
    return inputs.users.map(AssembleUserMapper);
  }
}
