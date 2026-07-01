import { FilterTaxRateByRegionMapper } from "../mappers/FilterTaxRateByRegionMapper.js";
import type {
  TaxRate_skip_id_,
  TaxRate_skip_value_,
  ListTaxRatesParams,
  TaxRate,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListTaxRatesResourceInputs extends SharedCollections {
  readonly taxRates: EagerCollection<TaxRate_skip_id_, TaxRate_skip_value_>;
}

export class ListTaxRatesResource implements Resource<ListTaxRatesResourceInputs> {
  private readonly region: string | null;

  constructor(params: ListTaxRatesParams) {
    this.region = params.region ?? null;
  }

  instantiate(
    inputs: ListTaxRatesResourceInputs,
    _context: Context,
  ): EagerCollection<TaxRate_skip_id_, TaxRate_skip_value_> {
    return inputs.taxRates.map(FilterTaxRateByRegionMapper, this.region);
  }
}
