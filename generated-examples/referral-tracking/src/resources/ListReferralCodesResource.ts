import { FilterReferralCodesMapper } from "../mappers/FilterReferralCodesMapper.js";
import type {
  ReferralCode_skip_id_,
  ReferralCode_skip_value_,
  ListReferralCodesParams,
  ReferralCode,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListReferralCodesResourceInputs extends SharedCollections {
  readonly referralCodes: EagerCollection<
    ReferralCode_skip_id_,
    ReferralCode_skip_value_
  >;
}

export class ListReferralCodesResource implements Resource<ListReferralCodesResourceInputs> {
  private readonly code: string | null;
  private readonly ownerId: string | null;
  private readonly status: string | null;

  constructor(params: ListReferralCodesParams) {
    this.code = params.code ?? null;
    this.ownerId = params.ownerId ?? null;
    this.status = params.status ?? null;
  }

  instantiate(
    inputs: ListReferralCodesResourceInputs,
    _context: Context,
  ): EagerCollection<ReferralCode_skip_id_, ReferralCode_skip_value_> {
    return inputs.referralCodes.map(
      FilterReferralCodesMapper,
      this.ownerId,
      this.code,
      this.status,
    );
  }
}
