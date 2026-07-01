import { FilterReferralCodesByOwnerAndStatusMapper } from "../mappers/FilterReferralCodesByOwnerAndStatusMapper.js";
import type {
  User_skip_id_,
  ReferralCode,
  ReferralCode_skip_id_,
  ListMyReferralCodesParams,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListMyReferralCodesResourceInputs extends SharedCollections {
  readonly referralCodesByOwner: EagerCollection<User_skip_id_, ReferralCode>;
}

export class ListMyReferralCodesResource implements Resource<ListMyReferralCodesResourceInputs> {
  private readonly status: string | null;
  private readonly userId: string;

  constructor(params: ListMyReferralCodesParams) {
    this.status = params.status ?? null;
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListMyReferralCodesResourceInputs,
    _context: Context,
  ): EagerCollection<ReferralCode_skip_id_, ReferralCode> {
    return inputs.referralCodesByOwner.map(
      FilterReferralCodesByOwnerAndStatusMapper,
      this.userId,
      this.status,
    );
  }
}
