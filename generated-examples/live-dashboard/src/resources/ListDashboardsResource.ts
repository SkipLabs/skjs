import { FilterDashboardsByOwnerMapper } from "../mappers/FilterDashboardsByOwnerMapper.js";
import type {
  Dashboard_skip_id_,
  DashboardStored,
  ListDashboardsParams,
  Dashboard,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListDashboardsResourceInputs extends SharedCollections {
  readonly dashboards: EagerCollection<Dashboard_skip_id_, DashboardStored>;
}

export class ListDashboardsResource implements Resource<ListDashboardsResourceInputs> {
  private readonly userId: string;

  constructor(params: ListDashboardsParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListDashboardsResourceInputs,
    _context: Context,
  ): EagerCollection<Dashboard_skip_id_, DashboardStored> {
    return inputs.dashboards.map(FilterDashboardsByOwnerMapper, this.userId);
  }
}
