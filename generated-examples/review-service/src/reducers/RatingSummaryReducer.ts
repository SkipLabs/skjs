import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { RatingValue, RatingSummaryAccum } from "../types.js";
import type { Reducer, Nullable } from "@skipruntime/core";

// add: returns a record whose count is the accumulator's count plus one; sum is the accumulator's sum plus the value; h1 is the accumulator's h1 plus one when the value equals 1 (otherwise unchanged); h2 is the accumulator's h2 plus one when the value equals 2 (otherwise unchanged); h3 is the accumulator's h3 plus one when the value equals 3 (otherwise unchanged); h4 is the accumulator's h4 plus one when the value equals 4 (otherwise unchanged); h5 is the accumulator's h5 plus one when the value equals 5 (otherwise unchanged). remove: returns a record whose count is the accumulator's count minus one; sum is the accumulator's sum minus the value; h1 is the accumulator's h1 minus one when the value equals 1 (otherwise unchanged); h2 is the accumulator's h2 minus one when the value equals 2 (otherwise unchanged); h3 is the accumulator's h3 minus one when the value equals 3 (otherwise unchanged); h4 is the accumulator's h4 minus one when the value equals 4 (otherwise unchanged); h5 is the accumulator's h5 minus one when the value equals 5 (otherwise unchanged).
export class RatingSummaryReducer implements Reducer<
  RatingValue,
  RatingSummaryAccum
> {
  initial: RatingSummaryAccum = {
    count: 0,
    sum: 0,
    h1: 0,
    h2: 0,
    h3: 0,
    h4: 0,
    h5: 0,
  };

  add(accum: RatingSummaryAccum, value: RatingValue): RatingSummaryAccum {
    // > add
    return {
      count: accum.count + 1,
      sum: accum.sum + value,
      h1: value === 1 ? accum.h1 + 1 : accum.h1,
      h2: value === 2 ? accum.h2 + 1 : accum.h2,
      h3: value === 3 ? accum.h3 + 1 : accum.h3,
      h4: value === 4 ? accum.h4 + 1 : accum.h4,
      h5: value === 5 ? accum.h5 + 1 : accum.h5,
    };
    // < add
  }

  remove(
    accum: RatingSummaryAccum,
    value: RatingValue,
  ): Nullable<RatingSummaryAccum> {
    // > remove
    return {
      count: accum.count - 1,
      sum: accum.sum - value,
      h1: value === 1 ? accum.h1 - 1 : accum.h1,
      h2: value === 2 ? accum.h2 - 1 : accum.h2,
      h3: value === 3 ? accum.h3 - 1 : accum.h3,
      h4: value === 4 ? accum.h4 - 1 : accum.h4,
      h5: value === 5 ? accum.h5 - 1 : accum.h5,
    };
    // < remove
  }
}
