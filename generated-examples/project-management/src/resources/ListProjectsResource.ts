import { FilterProjectByOwnerAndStatusMapper } from "../mappers/FilterProjectByOwnerAndStatusMapper.js";
import type {
  Project_skip_id_,
  Project_skip_value_,
  ListProjectsParams,
  Project,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListProjectsResourceInputs extends SharedCollections {
  readonly projects: EagerCollection<Project_skip_id_, Project_skip_value_>;
}

export class ListProjectsResource implements Resource<ListProjectsResourceInputs> {
  private readonly status: string | null;
  private readonly userId: string;

  constructor(params: ListProjectsParams) {
    this.status = params.status ?? null;
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListProjectsResourceInputs,
    _context: Context,
  ): EagerCollection<Project_skip_id_, Project_skip_value_> {
    return inputs.projects.map(
      FilterProjectByOwnerAndStatusMapper,
      this.userId,
      this.status,
    );
  }
}
