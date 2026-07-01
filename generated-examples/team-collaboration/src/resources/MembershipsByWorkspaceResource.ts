import { MembershipsByWorkspaceMapper } from "../mappers/MembershipsByWorkspaceMapper.js";
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
} from "@skipruntime/core";

export interface MembershipsByWorkspaceResourceInputs extends SharedCollections {
  readonly memberships: EagerCollection<MembershipKey, Membership_skip_value_>;
}

export class MembershipsByWorkspaceResource implements Resource<MembershipsByWorkspaceResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: MembershipsByWorkspaceResourceInputs,
    _context: Context,
  ): EagerCollection<Workspace_skip_id_, Membership> {
    const membershipsByWorkspace = inputs.memberships.map(
      MembershipsByWorkspaceMapper,
    );
    return membershipsByWorkspace;
  }
}
