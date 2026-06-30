import { ReferralCodeByCodeValueMapper } from "../mappers/ReferralCodeByCodeValueMapper.js";
import type {
  ReferralCode_skip_id_,
  ReferralCode_skip_value_,
  ReferralCodeValueKey,
  ReferralCode,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ReferralCodeByCodeValueResourceInputs extends SharedCollections {
  readonly referralCodes: EagerCollection<
    ReferralCode_skip_id_,
    ReferralCode_skip_value_
  >;
}

export class ReferralCodeByCodeValueResource implements Resource<ReferralCodeByCodeValueResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ReferralCodeByCodeValueResourceInputs,
    _context: Context,
  ): EagerCollection<ReferralCodeValueKey, ReferralCode> {
    return inputs.referralCodes.map(ReferralCodeByCodeValueMapper);
  }
}
