import type {
  Project_skip_id_,
  Project_skip_value_,
  Project,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetProjectResourceInputs extends SharedCollections {
  readonly projects: EagerCollection<Project_skip_id_, Project_skip_value_>;
}

export class GetProjectResource implements Resource<GetProjectResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetProjectResourceInputs,
    _context: Context,
  ): EagerCollection<Project_skip_id_, Project_skip_value_> {
    return inputs.projects;
  }
}
