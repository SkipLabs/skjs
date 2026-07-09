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
  Json,
} from "@skipruntime/core";

export interface ListActivitiesResourceInputs extends SharedCollections {
  readonly activities: EagerCollection<Activity_skip_id_, Activity_skip_value_>;
}

export class ListActivitiesResource implements Resource<ListActivitiesResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListActivitiesResourceInputs,
    _context: Context,
  ): EagerCollection<Activity_skip_id_, Activity_skip_value_> {
    return inputs.activities;
  }
}
