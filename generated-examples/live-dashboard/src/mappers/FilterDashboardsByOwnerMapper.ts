import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Dashboard_skip_id_,
  DashboardStored,
  Dashboard,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each dashboard entry, when the entry's value's ownerId field equals the userId param, emit the entry unchanged. Otherwise emit nothing.
export class FilterDashboardsByOwnerMapper implements Mapper<
  Dashboard_skip_id_,
  DashboardStored,
  Dashboard_skip_id_,
  DashboardStored
> {
  constructor(private userId: string) {}

  mapEntry(
    key: Dashboard_skip_id_,
    values: Values<DashboardStored>,
    context: Context,
  ): Iterable<[Dashboard_skip_id_, DashboardStored]> {
    // > body
    const emits: [Dashboard_skip_id_, DashboardStored][] = [];
    for (const value of values.toArray()) {
      if (value.ownerId === this.userId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
