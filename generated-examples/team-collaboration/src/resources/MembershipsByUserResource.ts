import { MembershipsByUserMapper } from "../mappers/MembershipsByUserMapper.js";
import type {
  MembershipKey,
  Membership_skip_value_,
  User_skip_id_,
  Membership,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface MembershipsByUserResourceInputs extends SharedCollections {
  readonly memberships: EagerCollection<MembershipKey, Membership_skip_value_>;
}

export class MembershipsByUserResource implements Resource<MembershipsByUserResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: MembershipsByUserResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, Membership> {
    const membershipsByUser = inputs.memberships.map(MembershipsByUserMapper);
    return membershipsByUser;
  }
}
