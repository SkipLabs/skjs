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
} from "@skipruntime/core";

export interface GetProjectStoredResourceInputs extends SharedCollections {
  readonly projects: EagerCollection<Project_skip_id_, Project_skip_value_>;
}

export class GetProjectStoredResource implements Resource<GetProjectStoredResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetProjectStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Project_skip_id_, Project_skip_value_> {
    return inputs.projects;
  }
}
