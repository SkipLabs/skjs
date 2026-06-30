import { GetUserByIdMapper } from "../mappers/GetUserByIdMapper.js";
import type {
  User_skip_id_,
  User_skip_value_,
  User,
  GetUserParams,
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

  constructor(params: GetUserParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: GetUserByIdResourceInputs,
    _context: Context,
  ): EagerCollection<0, User> {
    return inputs.users.map(GetUserByIdMapper, this.userId);
  }
}
