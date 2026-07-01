import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  TaxRule_skip_id_,
  TaxRule_skip_value_,
  TaxRule,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each tax rule entry, when the region param is absent, emit the entry unchanged. Otherwise emit the entry unchanged when the entry's value's region field equals the region param (case-sensitive, exact string match); emit nothing otherwise.
export class FilterTaxRuleByRegionMapper implements Mapper<
  TaxRule_skip_id_,
  TaxRule_skip_value_,
  TaxRule_skip_id_,
  TaxRule_skip_value_
> {
  constructor(private region: string | null) {}

  mapEntry(
    key: TaxRule_skip_id_,
    values: Values<TaxRule_skip_value_>,
    context: Context,
  ): Iterable<[TaxRule_skip_id_, TaxRule_skip_value_]> {
    // > body
    const emits: [TaxRule_skip_id_, TaxRule_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (this.region === null || value.region === this.region) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
