import { FilterUserByIdMapper } from "../mappers/FilterUserByIdMapper.js";
import type {
  User_skip_id_,
  User_skip_value_,
  GetUserByIdParams,
  User,
} from "../types.js";
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
  private readonly userId: string;

  constructor(params: GetUserByIdParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: GetUserByIdResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, User_skip_value_> {
    return inputs.users.map(FilterUserByIdMapper, this.userId);
  }
}
