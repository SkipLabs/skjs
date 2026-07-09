import type {
  MembershipKey,
  Membership_skip_value_,
  Membership,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetMembershipResourceInputs extends SharedCollections {
  readonly memberships: EagerCollection<MembershipKey, Membership_skip_value_>;
}

export class GetMembershipResource implements Resource<GetMembershipResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetMembershipResourceInputs,
    _context: Context,
  ): EagerCollection<MembershipKey, Membership_skip_value_> {
    return inputs.memberships;
  }
}
