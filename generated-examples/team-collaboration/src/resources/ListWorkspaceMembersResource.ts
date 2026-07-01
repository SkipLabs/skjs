import { MembershipByWorkspaceMapper } from "../mappers/MembershipByWorkspaceMapper.js";
import type {
  MembershipKey,
  Membership_skip_value_,
  Workspace_skip_id_,
  Membership,
  Workspace,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListWorkspaceMembersResourceInputs extends SharedCollections {
  readonly memberships: EagerCollection<MembershipKey, Membership_skip_value_>;
}

export class ListWorkspaceMembersResource implements Resource<ListWorkspaceMembersResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListWorkspaceMembersResourceInputs,
    _context: Context,
  ): EagerCollection<Workspace_skip_id_, Membership> {
    const membershipsByWorkspace = inputs.memberships.map(
      MembershipByWorkspaceMapper,
    );
    return membershipsByWorkspace;
  }
}
