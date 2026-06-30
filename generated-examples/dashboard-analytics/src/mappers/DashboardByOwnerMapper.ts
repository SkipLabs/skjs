import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Dashboard_skip_id_,
  Dashboard_skip_value_,
  User_skip_id_,
  Dashboard,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each dashboard entry, emit one output pair whose key is sourced from the entry's value's ownerId field (a User primary key) and whose value lists every required field of Dashboard explicitly — id sourced from the entry's key; ownerId sourced from the entry's value; name sourced from the entry's value; panels sourced from the entry's value; createdAt sourced from the entry's value; and every optional field with an explicit presence clause: description present when the entry's value's description field is present, sourced from the entry's value, absent otherwise; updatedAt present when the entry's value's updatedAt field is present, sourced from the entry's value, absent otherwise.
export class DashboardByOwnerMapper implements Mapper<
  Dashboard_skip_id_,
  Dashboard_skip_value_,
  User_skip_id_,
  Dashboard
> {
  mapEntry(
    key: Dashboard_skip_id_,
    values: Values<Dashboard_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, Dashboard]> {
    // > body
    const emits: [User_skip_id_, Dashboard][] = [];
    for (const value of values.toArray()) {
      const dashboard: Dashboard = {
        id: key,
        ownerId: value.ownerId,
        name: value.name,
        panels: value.panels,
        createdAt: value.createdAt,
        ...(value.description !== undefined && {
          description: value.description,
        }),
        ...(value.updatedAt !== undefined && { updatedAt: value.updatedAt }),
      };
      emits.push([value.ownerId, dashboard]);
    }
    return emits;
    // < body
  }
}
