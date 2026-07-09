import type {
  Referral_skip_id_,
  Referral_skip_value_,
  Referral,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetReferralResourceInputs extends SharedCollections {
  readonly referrals: EagerCollection<Referral_skip_id_, Referral_skip_value_>;
}

export class GetReferralResource implements Resource<GetReferralResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetReferralResourceInputs,
    _context: Context,
  ): EagerCollection<Referral_skip_id_, Referral_skip_value_> {
    return inputs.referrals;
  }
}
