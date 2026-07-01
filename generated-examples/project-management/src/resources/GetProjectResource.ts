import { FilterProjectByIdAndOwnerMapper } from "../mappers/FilterProjectByIdAndOwnerMapper.js";
import type {
  Project_skip_id_,
  Project_skip_value_,
  GetProjectParams,
  Project,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetProjectResourceInputs extends SharedCollections {
  readonly projects: EagerCollection<Project_skip_id_, Project_skip_value_>;
}

export class GetProjectResource implements Resource<GetProjectResourceInputs> {
  private readonly projectId: string;
  private readonly userId: string;

  constructor(params: GetProjectParams) {
    this.projectId = params.projectId;
    this.userId = params.userId;
  }

  instantiate(
    inputs: GetProjectResourceInputs,
    _context: Context,
  ): EagerCollection<Project_skip_id_, Project_skip_value_> {
    return inputs.projects.map(
      FilterProjectByIdAndOwnerMapper,
      this.userId,
      this.projectId,
    );
  }
}
