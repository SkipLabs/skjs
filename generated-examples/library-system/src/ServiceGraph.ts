import { ActiveLoanByBookMapper } from "./mappers/ActiveLoanByBookMapper.js";
import { SumReducer } from "./reducers/SumReducer.js";
import type {
  Book_skip_id_,
  Book,
  BookStored,
  Loan_skip_id_,
  Loan,
  Loan_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  ActiveLoanCount,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly booksStored: EagerCollection<Book_skip_id_, BookStored>;
  readonly loans: EagerCollection<Loan_skip_id_, Loan_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly activeLoanCountByBook: EagerCollection<
    Book_skip_id_,
    ActiveLoanCount
  >;
  readonly booksStored: EagerCollection<Book_skip_id_, BookStored>;
  readonly loans: EagerCollection<Loan_skip_id_, Loan_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const activeLoansByBook = inputs.loans.map(ActiveLoanByBookMapper);
  const activeLoanCountByBook = activeLoansByBook.reduce(SumReducer);
  const output_activeLoanCountByBook = activeLoanCountByBook;
  const output_booksStored = inputs.booksStored;
  const output_loans = inputs.loans;
  const output_users = inputs.users;
  return {
    activeLoanCountByBook: output_activeLoanCountByBook,
    booksStored: output_booksStored,
    loans: output_loans,
    users: output_users,
  };
}
