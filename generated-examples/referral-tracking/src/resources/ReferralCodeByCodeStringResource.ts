import type { ReferralCodeString, ReferralCodeStoredWithId } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ReferralCodeByCodeStringResourceInputs extends SharedCollections {
  readonly referralCodesByCodeString: EagerCollection<
    ReferralCodeString,
    ReferralCodeStoredWithId
  >;
}

export class ReferralCodeByCodeStringResource implements Resource<ReferralCodeByCodeStringResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ReferralCodeByCodeStringResourceInputs,
    _context: Context,
  ): EagerCollection<ReferralCodeString, ReferralCodeStoredWithId> {
    return inputs.referralCodesByCodeString;
  }
}
