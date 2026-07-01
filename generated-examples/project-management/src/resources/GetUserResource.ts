import { FilterUserByIdMapper } from "../mappers/FilterUserByIdMapper.js";
import type {
  User_skip_id_,
  User_skip_value_,
  GetUserParams,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetUserResourceInputs extends SharedCollections {
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export class GetUserResource implements Resource<GetUserResourceInputs> {
  private readonly userId: string;

  constructor(params: GetUserParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: GetUserResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, User_skip_value_> {
    return inputs.users.map(FilterUserByIdMapper, this.userId);
  }
}
