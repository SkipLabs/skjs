import type {
  Workspace_skip_id_,
  Workspace_skip_value_,
  Workspace,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetWorkspaceResourceInputs extends SharedCollections {
  readonly workspaces: EagerCollection<
    Workspace_skip_id_,
    Workspace_skip_value_
  >;
}

export class GetWorkspaceResource implements Resource<GetWorkspaceResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetWorkspaceResourceInputs,
    _context: Context,
  ): EagerCollection<Workspace_skip_id_, Workspace_skip_value_> {
    return inputs.workspaces;
  }
}
