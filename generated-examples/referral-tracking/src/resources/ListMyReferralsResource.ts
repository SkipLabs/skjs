import { FilterMyReferralsMapper } from "../mappers/FilterMyReferralsMapper.js";
import type {
  Referral_skip_id_,
  Referral_skip_value_,
  ListMyReferralsParams,
  Referral,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListMyReferralsResourceInputs extends SharedCollections {
  readonly referrals: EagerCollection<Referral_skip_id_, Referral_skip_value_>;
}

export class ListMyReferralsResource implements Resource<ListMyReferralsResourceInputs> {
  private readonly role: string | null;
  private readonly status: string | null;
  private readonly userId: string;

  constructor(params: ListMyReferralsParams) {
    this.role = params.role ?? null;
    this.status = params.status ?? null;
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListMyReferralsResourceInputs,
    _context: Context,
  ): EagerCollection<Referral_skip_id_, Referral_skip_value_> {
    return inputs.referrals.map(
      FilterMyReferralsMapper,
      this.userId,
      this.role,
      this.status,
    );
  }
}
