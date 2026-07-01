import { FilterReferralCodeByIdMapper } from "../mappers/FilterReferralCodeByIdMapper.js";
import type {
  ReferralCode_skip_id_,
  ReferralCode_skip_value_,
  GetReferralCodeByIdParams,
  ReferralCode,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetReferralCodeByIdResourceInputs extends SharedCollections {
  readonly referralCodes: EagerCollection<
    ReferralCode_skip_id_,
    ReferralCode_skip_value_
  >;
}

export class GetReferralCodeByIdResource implements Resource<GetReferralCodeByIdResourceInputs> {
  private readonly referralCodeId: string;

  constructor(params: GetReferralCodeByIdParams) {
    this.referralCodeId = params.referralCodeId;
  }

  instantiate(
    inputs: GetReferralCodeByIdResourceInputs,
    _context: Context,
  ): EagerCollection<ReferralCode_skip_id_, ReferralCode_skip_value_> {
    return inputs.referralCodes.map(
      FilterReferralCodeByIdMapper,
      this.referralCodeId,
    );
  }
}
