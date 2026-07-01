import { FilterGroupMembershipByGroupMapper } from "../mappers/FilterGroupMembershipByGroupMapper.js";
import type {
  Group_skip_id_,
  GroupMembershipByGroupValue,
  ListGroupMembersParams,
  Group,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListGroupMembersResourceInputs extends SharedCollections {
  readonly groupMembershipsByGroup: EagerCollection<
    Group_skip_id_,
    GroupMembershipByGroupValue
  >;
}

export class ListGroupMembersResource implements Resource<ListGroupMembersResourceInputs> {
  private readonly groupId: string;

  constructor(params: ListGroupMembersParams) {
    this.groupId = params.groupId;
  }

  instantiate(
    inputs: ListGroupMembersResourceInputs,
    _context: Context,
  ): EagerCollection<Group_skip_id_, GroupMembershipByGroupValue> {
    return inputs.groupMembershipsByGroup.map(
      FilterGroupMembershipByGroupMapper,
      this.groupId,
    );
  }
}
