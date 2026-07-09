import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { ProductPopularityCount } from "../types.js";
import type { Reducer, Nullable } from "@skipruntime/core";

// add: returns the accumulator plus the value. remove: returns the accumulator minus the value.
export class SumReducer implements Reducer<
  ProductPopularityCount,
  ProductPopularityCount
> {
  initial: ProductPopularityCount = 0;

  add(
    accum: ProductPopularityCount,
    value: ProductPopularityCount,
  ): ProductPopularityCount {
    // > add
    return accum + value;
    // < add
  }

  remove(
    accum: ProductPopularityCount,
    value: ProductPopularityCount,
  ): Nullable<ProductPopularityCount> {
    // > remove
    return accum - value;
    // < remove
  }
}
