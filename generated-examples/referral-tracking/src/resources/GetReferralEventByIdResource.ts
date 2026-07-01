import { FilterReferralEventByIdMapper } from "../mappers/FilterReferralEventByIdMapper.js";
import type {
  ReferralEvent_skip_id_,
  ReferralEvent_skip_value_,
  GetReferralEventByIdParams,
  ReferralEvent,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetReferralEventByIdResourceInputs extends SharedCollections {
  readonly referralEvents: EagerCollection<
    ReferralEvent_skip_id_,
    ReferralEvent_skip_value_
  >;
}

export class GetReferralEventByIdResource implements Resource<GetReferralEventByIdResourceInputs> {
  private readonly referralEventId: string;

  constructor(params: GetReferralEventByIdParams) {
    this.referralEventId = params.referralEventId;
  }

  instantiate(
    inputs: GetReferralEventByIdResourceInputs,
    _context: Context,
  ): EagerCollection<ReferralEvent_skip_id_, ReferralEvent_skip_value_> {
    return inputs.referralEvents.map(
      FilterReferralEventByIdMapper,
      this.referralEventId,
    );
  }
}
