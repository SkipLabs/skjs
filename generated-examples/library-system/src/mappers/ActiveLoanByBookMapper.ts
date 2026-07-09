import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Loan_skip_id_,
  Loan_skip_value_,
  Book_skip_id_,
  ActiveLoanCount,
  Loan,
  Book,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each loan entry, when the entry's status field equals the literal 'ACTIVE', emit one output pair whose key is sourced from the entry's bookId field and whose value is the literal one. Otherwise emit nothing. The original Loan.id is dropped: this collection feeds a sum reducer counting active loans per book, and the individual loan identity is not needed downstream.
export class ActiveLoanByBookMapper implements Mapper<
  Loan_skip_id_,
  Loan_skip_value_,
  Book_skip_id_,
  ActiveLoanCount
> {
  mapEntry(
    key: Loan_skip_id_,
    values: Values<Loan_skip_value_>,
    context: Context,
  ): Iterable<[Book_skip_id_, ActiveLoanCount]> {
    // > body
    const emits: [Book_skip_id_, ActiveLoanCount][] = [];
    for (const value of values.toArray()) {
      if (value.status === "ACTIVE") {
        emits.push([value.bookId, 1]);
      }
    }
    return emits;
    // < body
  }
}
