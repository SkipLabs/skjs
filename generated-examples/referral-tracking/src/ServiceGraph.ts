import { ReferralEventByCodeMapper } from "./mappers/ReferralEventByCodeMapper.js";
import { ReferralCodeStatsReducer } from "./reducers/ReferralCodeStatsReducer.js";
import type {
  ReferralCode_skip_id_,
  ReferralCode,
  ReferralCode_skip_value_,
  ReferralEvent_skip_id_,
  ReferralEvent,
  ReferralEvent_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  ReferralCodeStatsAccum,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly referralCodes: EagerCollection<
    ReferralCode_skip_id_,
    ReferralCode_skip_value_
  >;
  readonly referralEvents: EagerCollection<
    ReferralEvent_skip_id_,
    ReferralEvent_skip_value_
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly referralCodeStats: EagerCollection<
    ReferralCode_skip_id_,
    ReferralCodeStatsAccum
  >;
  readonly referralCodes: EagerCollection<
    ReferralCode_skip_id_,
    ReferralCode_skip_value_
  >;
  readonly referralEvents: EagerCollection<
    ReferralEvent_skip_id_,
    ReferralEvent_skip_value_
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const referralEventsByCode = inputs.referralEvents.map(
    ReferralEventByCodeMapper,
  );
  const referralCodeStatsAgg = referralEventsByCode.reduce(
    ReferralCodeStatsReducer,
  );
  const output_referralCodeStats = referralCodeStatsAgg;
  const output_referralCodes = inputs.referralCodes;
  const output_referralEvents = inputs.referralEvents;
  const output_users = inputs.users;
  return {
    referralCodeStats: output_referralCodeStats,
    referralCodes: output_referralCodes,
    referralEvents: output_referralEvents,
    users: output_users,
  };
}
