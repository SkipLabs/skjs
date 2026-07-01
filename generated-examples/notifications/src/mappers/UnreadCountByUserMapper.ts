import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  User_skip_id_,
  User_skip_value_,
  UnreadCount,
  UnreadTally,
  User,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each user entry, consult unreadOnesByUser for the values indexed by the entry's key — each consulted value is the literal one contributed by one unread notification for that user. Sum the consulted values to obtain the total unread count. Emit one output pair whose key is the entry's key and whose value is a record with a count field sourced from that sum. When no values are consulted (the user has no unread notifications), emit one output pair whose key is the entry's key and whose value is a record with a count field of zero. Every user in inputs.users yields exactly one entry.
export class UnreadCountByUserMapper implements Mapper<
  User_skip_id_,
  User_skip_value_,
  User_skip_id_,
  UnreadCount
> {
  constructor(
    private unreadOnesByUser: EagerCollection<User_skip_id_, UnreadTally>,
  ) {}

  mapEntry(
    key: User_skip_id_,
    values: Values<User_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, UnreadCount]> {
    // > body
    const tallies = this.unreadOnesByUser.getArray(key);
    let count = 0;
    for (const t of tallies) count += t;
    return [[key, { count }]];
    // < body
  }
}
