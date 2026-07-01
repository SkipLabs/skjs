import { WorkspacesForUserMapper } from "../mappers/WorkspacesForUserMapper.js";
import type {
  User_skip_id_,
  Membership,
  Workspace_skip_id_,
  Workspace_skip_value_,
  ListMyWorkspacesParams,
  User,
  Workspace,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListMyWorkspacesResourceInputs extends SharedCollections {
  readonly membershipsByUser: EagerCollection<User_skip_id_, Membership>;
  readonly workspaces: EagerCollection<
    Workspace_skip_id_,
    Workspace_skip_value_
  >;
}

export class ListMyWorkspacesResource implements Resource<ListMyWorkspacesResourceInputs> {
  private readonly userId: string;

  constructor(params: ListMyWorkspacesParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListMyWorkspacesResourceInputs,
    _context: Context,
  ): EagerCollection<Workspace_skip_id_, Workspace_skip_value_> {
    return inputs.workspaces.map(
      WorkspacesForUserMapper,
      this.userId,
      inputs.membershipsByUser,
    );
  }
}
