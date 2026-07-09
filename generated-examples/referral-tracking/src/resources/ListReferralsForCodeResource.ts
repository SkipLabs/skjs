import { FilterReferralsByCodeMapper } from "../mappers/FilterReferralsByCodeMapper.js";
import type {
  ReferralCode_skip_id_,
  Referral,
  Referral_skip_id_,
  ListReferralsForCodeParams,
  ReferralCode,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListReferralsForCodeResourceInputs extends SharedCollections {
  readonly referralsByCodeId: EagerCollection<ReferralCode_skip_id_, Referral>;
}

export class ListReferralsForCodeResource implements Resource<ListReferralsForCodeResourceInputs> {
  private readonly referralCodeId: string;
  private readonly since: string | null;
  private readonly status: string | null;
  private readonly until: string | null;

  constructor(params: ListReferralsForCodeParams) {
    this.referralCodeId = params.referralCodeId;
    this.since = params.since ?? null;
    this.status = params.status ?? null;
    this.until = params.until ?? null;
  }

  instantiate(
    inputs: ListReferralsForCodeResourceInputs,
    _context: Context,
  ): EagerCollection<Referral_skip_id_, Referral> {
    return inputs.referralsByCodeId.map(
      FilterReferralsByCodeMapper,
      this.referralCodeId,
      this.status,
      this.since,
      this.until,
    );
  }
}
