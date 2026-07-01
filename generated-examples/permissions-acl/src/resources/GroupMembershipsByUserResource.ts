import type {
  User_skip_id_,
  GroupMembershipByUserValue,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GroupMembershipsByUserResourceInputs extends SharedCollections {
  readonly groupMembershipsByUser: EagerCollection<
    User_skip_id_,
    GroupMembershipByUserValue
  >;
}

export class GroupMembershipsByUserResource implements Resource<GroupMembershipsByUserResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GroupMembershipsByUserResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, GroupMembershipByUserValue> {
    return inputs.groupMembershipsByUser;
  }
}
