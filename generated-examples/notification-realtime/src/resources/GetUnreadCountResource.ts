import type { User_skip_id_, UnreadCount, User } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetUnreadCountResourceInputs extends SharedCollections {
  readonly unreadCountByUser: EagerCollection<User_skip_id_, UnreadCount>;
}

export class GetUnreadCountResource implements Resource<GetUnreadCountResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetUnreadCountResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, UnreadCount> {
    return inputs.unreadCountByUser;
  }
}
