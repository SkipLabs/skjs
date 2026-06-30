import type {
  RoomMembershipKey,
  RoomMembership_skip_value_,
  RoomMembership,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface CheckMembershipResourceInputs extends SharedCollections {
  readonly memberships: EagerCollection<
    RoomMembershipKey,
    RoomMembership_skip_value_
  >;
}

export class CheckMembershipResource implements Resource<CheckMembershipResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: CheckMembershipResourceInputs,
    _context: Context,
  ): EagerCollection<RoomMembershipKey, RoomMembership_skip_value_> {
    return inputs.memberships;
  }
}
