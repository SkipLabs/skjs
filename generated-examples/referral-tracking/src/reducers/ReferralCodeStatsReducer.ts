import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ReferralEvent_skip_value_,
  ReferralCodeStatsAccum,
  ReferralEvent,
} from "../types.js";
import type { Reducer, Nullable } from "@skipruntime/core";

// add: returns a new accumulator whose clickCount is the accumulator's clickCount plus one when the value's kind equals the literal 'CLICK' (else unchanged); whose signupCount is the accumulator's signupCount plus one when the value's kind equals the literal 'SIGNUP' (else unchanged); whose activationCount is the accumulator's activationCount plus one when the value's kind equals the literal 'ACTIVATION' (else unchanged); whose rewardGrantedCount is the accumulator's rewardGrantedCount plus one when the value's kind equals the literal 'REWARD_GRANTED' (else unchanged); whose referredUserCounts is a copy of the accumulator's referredUserCounts with the entry at key value.referredUserId incremented by one (or set to one if absent). remove: returns a new accumulator whose clickCount is the accumulator's clickCount minus one when the value's kind equals the literal 'CLICK' (else unchanged); whose signupCount is the accumulator's signupCount minus one when the value's kind equals the literal 'SIGNUP' (else unchanged); whose activationCount is the accumulator's activationCount minus one when the value's kind equals the literal 'ACTIVATION' (else unchanged); whose rewardGrantedCount is the accumulator's rewardGrantedCount minus one when the value's kind equals the literal 'REWARD_GRANTED' (else unchanged); whose referredUserCounts is a copy of the accumulator's referredUserCounts with the entry at key value.referredUserId decremented by one, and removed from the map when the count reaches zero.
export class ReferralCodeStatsReducer implements Reducer<
  ReferralEvent_skip_value_,
  ReferralCodeStatsAccum
> {
  initial: ReferralCodeStatsAccum = {
    clickCount: 0,
    signupCount: 0,
    activationCount: 0,
    rewardGrantedCount: 0,
    referredUserCounts: {},
  };

  add(
    accum: ReferralCodeStatsAccum,
    value: ReferralEvent_skip_value_,
  ): ReferralCodeStatsAccum {
    // > add
    const referredUserCounts: Record<string, number> = {};
    for (const k of Object.keys(accum.referredUserCounts)) {
      const v = accum.referredUserCounts[k];
      if (v !== undefined) referredUserCounts[k] = v;
    }
    const existing = referredUserCounts[value.referredUserId];
    referredUserCounts[value.referredUserId] =
      existing === undefined ? 1 : existing + 1;
    return {
      clickCount:
        value.kind === "CLICK" ? accum.clickCount + 1 : accum.clickCount,
      signupCount:
        value.kind === "SIGNUP" ? accum.signupCount + 1 : accum.signupCount,
      activationCount:
        value.kind === "ACTIVATION"
          ? accum.activationCount + 1
          : accum.activationCount,
      rewardGrantedCount:
        value.kind === "REWARD_GRANTED"
          ? accum.rewardGrantedCount + 1
          : accum.rewardGrantedCount,
      referredUserCounts,
    };
    // < add
  }

  remove(
    accum: ReferralCodeStatsAccum,
    value: ReferralEvent_skip_value_,
  ): Nullable<ReferralCodeStatsAccum> {
    // > remove
    const referredUserCounts: Record<string, number> = {};
    for (const k of Object.keys(accum.referredUserCounts)) {
      const v = accum.referredUserCounts[k];
      if (v !== undefined) referredUserCounts[k] = v;
    }
    const existing = referredUserCounts[value.referredUserId];
    const newCount = (existing === undefined ? 0 : existing) - 1;
    if (newCount <= 0) {
      delete referredUserCounts[value.referredUserId];
    } else {
      referredUserCounts[value.referredUserId] = newCount;
    }
    return {
      clickCount:
        value.kind === "CLICK" ? accum.clickCount - 1 : accum.clickCount,
      signupCount:
        value.kind === "SIGNUP" ? accum.signupCount - 1 : accum.signupCount,
      activationCount:
        value.kind === "ACTIVATION"
          ? accum.activationCount - 1
          : accum.activationCount,
      rewardGrantedCount:
        value.kind === "REWARD_GRANTED"
          ? accum.rewardGrantedCount - 1
          : accum.rewardGrantedCount,
      referredUserCounts,
    };
    // < remove
  }
}
