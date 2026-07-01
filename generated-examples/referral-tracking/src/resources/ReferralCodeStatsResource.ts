import type {
  ReferralCode_skip_id_,
  ReferralCodeStatsAccum,
  ReferralCode,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ReferralCodeStatsResourceInputs extends SharedCollections {
  readonly referralCodeStats: EagerCollection<
    ReferralCode_skip_id_,
    ReferralCodeStatsAccum
  >;
}

export class ReferralCodeStatsResource implements Resource<ReferralCodeStatsResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ReferralCodeStatsResourceInputs,
    _context: Context,
  ): EagerCollection<ReferralCode_skip_id_, ReferralCodeStatsAccum> {
    return inputs.referralCodeStats;
  }
}
