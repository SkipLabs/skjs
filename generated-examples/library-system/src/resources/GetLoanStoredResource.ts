import type { Loan_skip_id_, Loan_skip_value_, Loan } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetLoanStoredResourceInputs extends SharedCollections {
  readonly loans: EagerCollection<Loan_skip_id_, Loan_skip_value_>;
}

export class GetLoanStoredResource implements Resource<GetLoanStoredResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetLoanStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Loan_skip_id_, Loan_skip_value_> {
    return inputs.loans;
  }
}
