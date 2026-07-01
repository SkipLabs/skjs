import type {
  TaxRate_skip_id_,
  TaxRate_skip_value_,
  TaxRate,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetTaxRateResourceInputs extends SharedCollections {
  readonly taxRates: EagerCollection<TaxRate_skip_id_, TaxRate_skip_value_>;
}

export class GetTaxRateResource implements Resource<GetTaxRateResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetTaxRateResourceInputs,
    _context: Context,
  ): EagerCollection<TaxRate_skip_id_, TaxRate_skip_value_> {
    return inputs.taxRates;
  }
}
