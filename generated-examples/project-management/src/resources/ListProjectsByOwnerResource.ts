import { ProjectByOwnerKeepIdMapper } from "../mappers/ProjectByOwnerKeepIdMapper.js";
import type {
  Project_skip_id_,
  Project_skip_value_,
  User_skip_id_,
  Project,
  ListProjectsParams,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListProjectsByOwnerResourceInputs extends SharedCollections {
  readonly projects: EagerCollection<Project_skip_id_, Project_skip_value_>;
}

export class ListProjectsByOwnerResource implements Resource<ListProjectsByOwnerResourceInputs> {
  private readonly userId: string;

  constructor(params: ListProjectsParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListProjectsByOwnerResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, Project> {
    return inputs.projects.map(ProjectByOwnerKeepIdMapper, this.userId);
  }
}
