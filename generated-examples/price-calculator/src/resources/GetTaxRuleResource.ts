import { SingleTaxRuleByIdMapper } from "../mappers/SingleTaxRuleByIdMapper.js";
import type {
  TaxRule_skip_id_,
  TaxRule_skip_value_,
  GetTaxRuleParams,
  TaxRule,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetTaxRuleResourceInputs extends SharedCollections {
  readonly taxRules: EagerCollection<TaxRule_skip_id_, TaxRule_skip_value_>;
}

export class GetTaxRuleResource implements Resource<GetTaxRuleResourceInputs> {
  private readonly taxRuleId: string;

  constructor(params: GetTaxRuleParams) {
    this.taxRuleId = params.taxRuleId;
  }

  instantiate(
    inputs: GetTaxRuleResourceInputs,
    _context: Context,
  ): EagerCollection<TaxRule_skip_id_, TaxRule_skip_value_> {
    return inputs.taxRules.map(SingleTaxRuleByIdMapper, this.taxRuleId);
  }
}
