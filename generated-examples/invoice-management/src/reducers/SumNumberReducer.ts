import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { InvoiceAmount } from "../types.js";
import type { Reducer, Nullable } from "@skipruntime/core";

// add: returns the accumulator plus the value. remove: returns the accumulator minus the value.
export class SumNumberReducer implements Reducer<InvoiceAmount, InvoiceAmount> {
  initial: InvoiceAmount = 0;

  add(accum: InvoiceAmount, value: InvoiceAmount): InvoiceAmount {
    // > add
    return accum + value;
    // < add
  }

  remove(accum: InvoiceAmount, value: InvoiceAmount): Nullable<InvoiceAmount> {
    // > remove
    return accum - value;
    // < remove
  }
}
