import type {
  Activity_skip_id_,
  Activity_skip_value_,
  Activity,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetActivityByIdResourceInputs extends SharedCollections {
  readonly activities: EagerCollection<Activity_skip_id_, Activity_skip_value_>;
}

export class GetActivityByIdResource implements Resource<GetActivityByIdResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetActivityByIdResourceInputs,
    _context: Context,
  ): EagerCollection<Activity_skip_id_, Activity_skip_value_> {
    return inputs.activities;
  }
}
