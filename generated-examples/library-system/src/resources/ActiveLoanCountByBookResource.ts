import type { Book_skip_id_, ActiveLoanCount, Book } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ActiveLoanCountByBookResourceInputs extends SharedCollections {
  readonly activeLoanCountByBook: EagerCollection<
    Book_skip_id_,
    ActiveLoanCount
  >;
}

export class ActiveLoanCountByBookResource implements Resource<ActiveLoanCountByBookResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ActiveLoanCountByBookResourceInputs,
    _context: Context,
  ): EagerCollection<Book_skip_id_, ActiveLoanCount> {
    return inputs.activeLoanCountByBook;
  }
}
