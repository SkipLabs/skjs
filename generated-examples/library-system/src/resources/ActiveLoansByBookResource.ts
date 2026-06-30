import { ActiveLoansByBookMapper } from "../mappers/ActiveLoansByBookMapper.js";
import type {
  Loan_skip_id_,
  Loan_skip_value_,
  Book_skip_id_,
  Loan,
  Book,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ActiveLoansByBookResourceInputs extends SharedCollections {
  readonly loans: EagerCollection<Loan_skip_id_, Loan_skip_value_>;
}

export class ActiveLoansByBookResource implements Resource<ActiveLoansByBookResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ActiveLoansByBookResourceInputs,
    _context: Context,
  ): EagerCollection<Book_skip_id_, Loan_skip_value_> {
    const activeLoansByBook = inputs.loans.map(ActiveLoansByBookMapper);
    return activeLoansByBook;
  }
}
