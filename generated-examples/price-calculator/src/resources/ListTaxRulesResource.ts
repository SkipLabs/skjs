import { FilterTaxRuleByRegionMapper } from "../mappers/FilterTaxRuleByRegionMapper.js";
import type {
  TaxRule_skip_id_,
  TaxRule_skip_value_,
  ListTaxRulesParams,
  TaxRule,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListTaxRulesResourceInputs extends SharedCollections {
  readonly taxRules: EagerCollection<TaxRule_skip_id_, TaxRule_skip_value_>;
}

export class ListTaxRulesResource implements Resource<ListTaxRulesResourceInputs> {
  private readonly region: string | null;

  constructor(params: ListTaxRulesParams) {
    this.region = params.region ?? null;
  }

  instantiate(
    inputs: ListTaxRulesResourceInputs,
    _context: Context,
  ): EagerCollection<TaxRule_skip_id_, TaxRule_skip_value_> {
    return inputs.taxRules.map(FilterTaxRuleByRegionMapper, this.region);
  }
}
