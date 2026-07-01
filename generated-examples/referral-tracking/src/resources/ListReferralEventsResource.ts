import { FilterReferralEventsMapper } from "../mappers/FilterReferralEventsMapper.js";
import type {
  ReferralEvent_skip_id_,
  ReferralEvent_skip_value_,
  ListReferralEventsParams,
  ReferralEvent,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListReferralEventsResourceInputs extends SharedCollections {
  readonly referralEvents: EagerCollection<
    ReferralEvent_skip_id_,
    ReferralEvent_skip_value_
  >;
}

export class ListReferralEventsResource implements Resource<ListReferralEventsResourceInputs> {
  private readonly kind: string | null;
  private readonly referralCodeId: string | null;
  private readonly referredUserId: string | null;
  private readonly referrerUserId: string | null;

  constructor(params: ListReferralEventsParams) {
    this.kind = params.kind ?? null;
    this.referralCodeId = params.referralCodeId ?? null;
    this.referredUserId = params.referredUserId ?? null;
    this.referrerUserId = params.referrerUserId ?? null;
  }

  instantiate(
    inputs: ListReferralEventsResourceInputs,
    _context: Context,
  ): EagerCollection<ReferralEvent_skip_id_, ReferralEvent_skip_value_> {
    return inputs.referralEvents.map(
      FilterReferralEventsMapper,
      this.referralCodeId,
      this.referrerUserId,
      this.referredUserId,
      this.kind,
    );
  }
}
