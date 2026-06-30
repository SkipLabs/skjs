import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  User_skip_id_,
  User_skip_value_,
  UnreadCount,
  UnreadMarker,
  User,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each user entry, emit nothing when the entry's key does not equal the userId param. Otherwise consult unreadByRecipient for the values indexed by the userId param to obtain every 1-marker for the user's unread notifications. Sum the consulted values (defaulting to zero when no values are consulted). Emit one output pair whose key is the literal-zero key and whose value lists every required field of UnreadCount explicitly — count sourced from the computed sum.
export class UnreadCountByUserMapper implements Mapper<
  User_skip_id_,
  User_skip_value_,
  0,
  UnreadCount
> {
  constructor(
    private userId: string,
    private unreadByRecipient: EagerCollection<User_skip_id_, UnreadMarker>,
  ) {}

  mapEntry(
    key: User_skip_id_,
    values: Values<User_skip_value_>,
    context: Context,
  ): Iterable<[0, UnreadCount]> {
    // > body
    if (key !== this.userId) return [];
    const markers = this.unreadByRecipient.getArray(this.userId);
    let count = 0;
    for (const marker of markers) count += marker;
    const result: UnreadCount = { count };
    return [[0, result]];
    // < body
  }
}
