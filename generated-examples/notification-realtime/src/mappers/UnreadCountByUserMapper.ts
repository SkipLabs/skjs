import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  User_skip_id_,
  User_skip_value_,
  UnreadCount,
  UnreadOne,
  User,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each user entry, consult unreadOnesByUser for the values indexed by the entry's key — each consulted value is the literal one representing one unread notification. Count the number of consulted values (equivalently, sum them since each is one) and emit one output pair whose key is the entry's key and whose value is that count. When no values are consulted (the user has no unread notifications), emit one output pair whose key is the entry's key and whose value is zero. Every user in inputs.users yields exactly one entry.
export class UnreadCountByUserMapper implements Mapper<
  User_skip_id_,
  User_skip_value_,
  User_skip_id_,
  UnreadCount
> {
  constructor(
    private unreadOnesByUser: EagerCollection<User_skip_id_, UnreadOne>,
  ) {}

  mapEntry(
    key: User_skip_id_,
    values: Values<User_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, UnreadCount]> {
    // > body
    const unreadValues = this.unreadOnesByUser.getArray(key);
    let count = 0;
    for (const v of unreadValues) count += v;
    return [[key, count]];
    // < body
  }
}
