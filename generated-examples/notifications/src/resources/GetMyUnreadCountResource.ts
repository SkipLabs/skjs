import { UnreadCountForUserMapper } from "../mappers/UnreadCountForUserMapper.js";
import type {
  RecipientUserId,
  UnreadCountAccum,
  UnreadCount,
  UnreadCountParams,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetMyUnreadCountResourceInputs extends SharedCollections {
  readonly unreadCountByRecipient: EagerCollection<
    RecipientUserId,
    UnreadCountAccum
  >;
}

export class GetMyUnreadCountResource implements Resource<GetMyUnreadCountResourceInputs> {
  private readonly userId: string;

  constructor(params: UnreadCountParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: GetMyUnreadCountResourceInputs,
    _context: Context,
  ): EagerCollection<0, UnreadCount> {
    return inputs.unreadCountByRecipient.map(
      UnreadCountForUserMapper,
      this.userId,
    );
  }
}
