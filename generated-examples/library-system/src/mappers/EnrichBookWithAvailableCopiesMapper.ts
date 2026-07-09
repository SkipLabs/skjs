import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Book_skip_id_,
  BookStored,
  Book_skip_value_,
  ActiveLoanCount,
  Book,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each book entry, consult activeLoanCountByBook for the values indexed by the entry's key; sum the consulted values (defaulting to zero when no values are consulted) to obtain the active loan count. Emit one output pair whose key is the entry's key and whose value lists every required field of Book explicitly: id sourced from the entry's key; title sourced from the entry's value's title field; author sourced from the entry's value's author field; totalCopies sourced from the entry's value's totalCopies field; createdAt sourced from the entry's value's createdAt field; availableCopies computed as the entry's value's totalCopies field minus the active loan count (never below zero); isbn present when the entry's value's isbn field is present, sourced from the entry's value's isbn field, absent otherwise.
export class EnrichBookWithAvailableCopiesMapper implements Mapper<
  Book_skip_id_,
  BookStored,
  Book_skip_id_,
  Book_skip_value_
> {
  constructor(
    private activeLoanCountByBook: EagerCollection<
      Book_skip_id_,
      ActiveLoanCount
    >,
  ) {}

  mapEntry(
    key: Book_skip_id_,
    values: Values<BookStored>,
    context: Context,
  ): Iterable<[Book_skip_id_, Book_skip_value_]> {
    // > body
    const emits: [Book_skip_id_, Book_skip_value_][] = [];
    for (const stored of values.toArray()) {
      const loanCounts = this.activeLoanCountByBook.getArray(key);
      let activeLoans = 0;
      for (const c of loanCounts) activeLoans += c;
      const available = stored.totalCopies - activeLoans;
      const availableCopies = available < 0 ? 0 : available;
      const value: Book_skip_value_ = {
        author: stored.author,
        availableCopies,
        createdAt: stored.createdAt,
        title: stored.title,
        totalCopies: stored.totalCopies,
        ...(stored.isbn !== undefined && { isbn: stored.isbn }),
      };
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
