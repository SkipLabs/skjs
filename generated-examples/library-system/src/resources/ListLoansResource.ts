import { ListLoansByUserMapper } from "../mappers/ListLoansByUserMapper.js";
import type {
  Loan_skip_id_,
  Loan_skip_value_,
  ListLoansParams,
  Loan,
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
  private readonly userId: string;

  constructor(params: ListLoansParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListLoansResourceInputs,
    _context: Context,
  ): EagerCollection<Loan_skip_id_, Loan_skip_value_> {
    return inputs.loans.map(ListLoansByUserMapper, this.userId);
  }
}
