import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  TaxRule_skip_id_,
  TaxRule_skip_value_,
  TaxRule,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each tax rule entry, emit the entry unchanged when the entry's key equals the taxRuleId param. Otherwise emit nothing.
export class SingleTaxRuleByIdMapper implements Mapper<
  TaxRule_skip_id_,
  TaxRule_skip_value_,
  TaxRule_skip_id_,
  TaxRule_skip_value_
> {
  constructor(private taxRuleId: string) {}

  mapEntry(
    key: TaxRule_skip_id_,
    values: Values<TaxRule_skip_value_>,
    context: Context,
  ): Iterable<[TaxRule_skip_id_, TaxRule_skip_value_]> {
    // > body
    if (key === this.taxRuleId) {
      const emits: [TaxRule_skip_id_, TaxRule_skip_value_][] = [];
      for (const value of values.toArray()) {
        emits.push([key, value]);
      }
      return emits;
    }
    return [];
    // < body
  }
}
