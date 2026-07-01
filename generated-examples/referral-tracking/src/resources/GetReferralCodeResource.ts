import type {
  ReferralCode_skip_id_,
  ReferralCode_skip_value_,
  ReferralCode,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetReferralCodeResourceInputs extends SharedCollections {
  readonly referralCodesAssembled: EagerCollection<
    ReferralCode_skip_id_,
    ReferralCode_skip_value_
  >;
}

export class GetReferralCodeResource implements Resource<GetReferralCodeResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetReferralCodeResourceInputs,
    _context: Context,
  ): EagerCollection<ReferralCode_skip_id_, ReferralCode_skip_value_> {
    return inputs.referralCodesAssembled;
  }
}
