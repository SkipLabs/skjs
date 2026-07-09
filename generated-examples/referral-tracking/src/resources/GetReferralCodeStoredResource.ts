import type {
  ReferralCode_skip_id_,
  ReferralCodeStored,
  ReferralCode,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetReferralCodeStoredResourceInputs extends SharedCollections {
  readonly referralCodes: EagerCollection<
    ReferralCode_skip_id_,
    ReferralCodeStored
  >;
}

export class GetReferralCodeStoredResource implements Resource<GetReferralCodeStoredResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetReferralCodeStoredResourceInputs,
    _context: Context,
  ): EagerCollection<ReferralCode_skip_id_, ReferralCodeStored> {
    return inputs.referralCodes;
  }
}
