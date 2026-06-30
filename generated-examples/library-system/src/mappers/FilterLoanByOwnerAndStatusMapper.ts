import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Loan_skip_id_, Loan_skip_value_, Loan } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each loan entry, when the entry's value's borrowerId field does not equal the userId param, emit nothing. When the status param is present and does not equal the entry's value's status field, emit nothing. Otherwise emit one output pair whose key is the entry's key and whose value lists every required field of Loan explicitly — id sourced from the entry's key; bookId, borrowerId, status, borrowedAt, dueAt sourced from the entry's value; and the optional field returnedAt, present when the entry's value carries a returnedAt field, sourced from the entry's value, absent otherwise.
export class FilterLoanByOwnerAndStatusMapper implements Mapper<
  Loan_skip_id_,
  Loan_skip_value_,
  Loan_skip_id_,
  Loan
> {
  constructor(
    private userId: string,
    private status: string | null,
  ) {}

  mapEntry(
    key: Loan_skip_id_,
    values: Values<Loan_skip_value_>,
    context: Context,
  ): Iterable<[Loan_skip_id_, Loan]> {
    // > body
    const emits: [Loan_skip_id_, Loan][] = [];
    for (const value of values.toArray()) {
      if (value.borrowerId !== this.userId) continue;
      if (this.status !== null && value.status !== this.status) continue;
      const loan: Loan = {
        id: key,
        bookId: value.bookId,
        borrowerId: value.borrowerId,
        status: value.status,
        borrowedAt: value.borrowedAt,
        dueAt: value.dueAt,
        ...(value.returnedAt !== undefined && { returnedAt: value.returnedAt }),
      };
      emits.push([key, loan]);
    }
    return emits;
    // < body
  }
}
