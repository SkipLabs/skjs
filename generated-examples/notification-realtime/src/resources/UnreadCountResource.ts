import { UnreadCountByUserMapper } from "../mappers/UnreadCountByUserMapper.js";
import type {
  User_skip_id_,
  UnreadMarker,
  User_skip_value_,
  UnreadCount,
  UnreadCountParams,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface UnreadCountResourceInputs extends SharedCollections {
  readonly unreadByRecipient: EagerCollection<User_skip_id_, UnreadMarker>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export class UnreadCountResource implements Resource<UnreadCountResourceInputs> {
  private readonly userId: string;

  constructor(params: UnreadCountParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: UnreadCountResourceInputs,
    _context: Context,
  ): EagerCollection<0, UnreadCount> {
    return inputs.users.map(
      UnreadCountByUserMapper,
      this.userId,
      inputs.unreadByRecipient,
    );
  }
}
