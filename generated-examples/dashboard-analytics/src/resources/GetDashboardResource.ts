import type {
  Dashboard_skip_id_,
  Dashboard_skip_value_,
  Dashboard,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetDashboardResourceInputs extends SharedCollections {
  readonly dashboards: EagerCollection<
    Dashboard_skip_id_,
    Dashboard_skip_value_
  >;
}

export class GetDashboardResource implements Resource<GetDashboardResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetDashboardResourceInputs,
    _context: Context,
  ): EagerCollection<Dashboard_skip_id_, Dashboard_skip_value_> {
    return inputs.dashboards;
  }
}
