import { LoanByIdWithOwnerCheckMapper } from "../mappers/LoanByIdWithOwnerCheckMapper.js";
import type {
  Loan_skip_id_,
  Loan_skip_value_,
  GetLoanParams,
  Loan,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetLoanResourceInputs extends SharedCollections {
  readonly loans: EagerCollection<Loan_skip_id_, Loan_skip_value_>;
}

export class GetLoanResource implements Resource<GetLoanResourceInputs> {
  private readonly loanId: string;
  private readonly userId: string;

  constructor(params: GetLoanParams) {
    this.loanId = params.loanId;
    this.userId = params.userId;
  }

  instantiate(
    inputs: GetLoanResourceInputs,
    _context: Context,
  ): EagerCollection<Loan_skip_id_, Loan_skip_value_> {
    return inputs.loans.map(
      LoanByIdWithOwnerCheckMapper,
      this.loanId,
      this.userId,
    );
  }
}
