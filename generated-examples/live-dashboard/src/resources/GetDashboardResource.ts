import type {
  Dashboard_skip_id_,
  DashboardStored,
  Dashboard,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetDashboardResourceInputs extends SharedCollections {
  readonly dashboards: EagerCollection<Dashboard_skip_id_, DashboardStored>;
}

export class GetDashboardResource implements Resource<GetDashboardResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetDashboardResourceInputs,
    _context: Context,
  ): EagerCollection<Dashboard_skip_id_, DashboardStored> {
    return inputs.dashboards;
  }
}
