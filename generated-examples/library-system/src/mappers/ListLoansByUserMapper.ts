import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Loan_skip_id_, Loan_skip_value_, Loan } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each loan entry, when the entry's value's borrowerId field equals the userId param, emit the entry unchanged. Otherwise emit nothing.
export class ListLoansByUserMapper implements Mapper<
  Loan_skip_id_,
  Loan_skip_value_,
  Loan_skip_id_,
  Loan_skip_value_
> {
  constructor(private userId: string) {}

  mapEntry(
    key: Loan_skip_id_,
    values: Values<Loan_skip_value_>,
    context: Context,
  ): Iterable<[Loan_skip_id_, Loan_skip_value_]> {
    // > body
    const emits: [Loan_skip_id_, Loan_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (value.borrowerId === this.userId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
