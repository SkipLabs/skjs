import { DashboardByOwnerMapper } from "../mappers/DashboardByOwnerMapper.js";
import type {
  Dashboard_skip_id_,
  Dashboard_skip_value_,
  User_skip_id_,
  Dashboard,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListDashboardsByOwnerResourceInputs extends SharedCollections {
  readonly dashboards: EagerCollection<
    Dashboard_skip_id_,
    Dashboard_skip_value_
  >;
}

export class ListDashboardsByOwnerResource implements Resource<ListDashboardsByOwnerResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListDashboardsByOwnerResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, Dashboard> {
    const dashboardsByOwner = inputs.dashboards.map(DashboardByOwnerMapper);
    return dashboardsByOwner;
  }
}
