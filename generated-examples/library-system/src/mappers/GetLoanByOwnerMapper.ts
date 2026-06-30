import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Loan_skip_id_, Loan_skip_value_, Loan } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each loan entry, when the entry's key does not equal the loanId param, emit nothing. When the entry's value's borrowerId field does not equal the userId param, emit nothing. Otherwise emit one output pair whose key is the literal zero and whose value lists every required field of Loan explicitly — id sourced from the entry's key; bookId, borrowerId, status, borrowedAt, dueAt sourced from the entry's value; and the optional field returnedAt, present when the entry's value carries a returnedAt field, sourced from the entry's value, absent otherwise.
export class GetLoanByOwnerMapper implements Mapper<
  Loan_skip_id_,
  Loan_skip_value_,
  0,
  Loan
> {
  constructor(
    private loanId: string,
    private userId: string,
  ) {}

  mapEntry(
    key: Loan_skip_id_,
    values: Values<Loan_skip_value_>,
    context: Context,
  ): Iterable<[0, Loan]> {
    // > body
    if (key !== this.loanId) return [];
    const emits: [0, Loan][] = [];
    for (const value of values.toArray()) {
      if (value.borrowerId !== this.userId) continue;
      const loan: Loan = {
        id: key,
        bookId: value.bookId,
        borrowerId: value.borrowerId,
        status: value.status,
        borrowedAt: value.borrowedAt,
        dueAt: value.dueAt,
        ...(value.returnedAt !== undefined && { returnedAt: value.returnedAt }),
      };
      emits.push([0, loan]);
    }
    return emits;
    // < body
  }
}
