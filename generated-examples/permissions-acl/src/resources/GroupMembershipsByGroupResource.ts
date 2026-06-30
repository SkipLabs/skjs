import type {
  Group_skip_id_,
  GroupMembershipByGroupValue,
  Group,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GroupMembershipsByGroupResourceInputs extends SharedCollections {
  readonly groupMembershipsByGroup: EagerCollection<
    Group_skip_id_,
    GroupMembershipByGroupValue
  >;
}

export class GroupMembershipsByGroupResource implements Resource<GroupMembershipsByGroupResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GroupMembershipsByGroupResourceInputs,
    _context: Context,
  ): EagerCollection<Group_skip_id_, GroupMembershipByGroupValue> {
    return inputs.groupMembershipsByGroup;
  }
}
