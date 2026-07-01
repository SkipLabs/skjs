import { FilterLoanByOwnerAndStatusMapper } from "../mappers/FilterLoanByOwnerAndStatusMapper.js";
import type {
  Loan_skip_id_,
  Loan_skip_value_,
  Loan,
  ListLoansParams,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListLoansResourceInputs extends SharedCollections {
  readonly loans: EagerCollection<Loan_skip_id_, Loan_skip_value_>;
}

export class ListLoansResource implements Resource<ListLoansResourceInputs> {
  private readonly status: string | null;
  private readonly userId: string;

  constructor(params: ListLoansParams) {
    this.status = params.status ?? null;
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListLoansResourceInputs,
    _context: Context,
  ): EagerCollection<Loan_skip_id_, Loan> {
    return inputs.loans.map(
      FilterLoanByOwnerAndStatusMapper,
      this.userId,
      this.status,
    );
  }
}
