import type {
  Book_skip_id_,
  Book,
  Book_skip_value_,
  Loan_skip_id_,
  Loan,
  Loan_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly books: EagerCollection<Book_skip_id_, Book_skip_value_>;
  readonly loans: EagerCollection<Loan_skip_id_, Loan_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly books: EagerCollection<Book_skip_id_, Book_skip_value_>;
  readonly loans: EagerCollection<Loan_skip_id_, Loan_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_books = inputs.books;
  const output_loans = inputs.loans;
  const output_users = inputs.users;
  return { books: output_books, loans: output_loans, users: output_users };
}
