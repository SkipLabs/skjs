import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Loan_skip_id_,
  Loan_skip_value_,
  Book_skip_id_,
  Loan,
  Book,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each loan entry, when the entry's value's status field does not equal the literal 'ACTIVE', emit nothing. Otherwise emit one output pair whose key is sourced from the entry's value's bookId field and whose value is the entry's value unchanged. The original loan id is dropped because the consumer (book deletion conflict check) only needs to know whether any active loan exists for a given bookId, not which loan it is.
export class ActiveLoansByBookMapper implements Mapper<
  Loan_skip_id_,
  Loan_skip_value_,
  Book_skip_id_,
  Loan_skip_value_
> {
  mapEntry(
    key: Loan_skip_id_,
    values: Values<Loan_skip_value_>,
    context: Context,
  ): Iterable<[Book_skip_id_, Loan_skip_value_]> {
    // > body
    const emits: [Book_skip_id_, Loan_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (value.status !== "ACTIVE") continue;
      emits.push([value.bookId, value]);
    }
    return emits;
    // < body
  }
}
