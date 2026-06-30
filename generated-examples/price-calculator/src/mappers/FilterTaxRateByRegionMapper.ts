import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  TaxRate_skip_id_,
  TaxRate_skip_value_,
  TaxRate,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry, emit the entry unchanged when the region param is absent OR the entry's region field equals the region param exactly. Otherwise emit nothing.
export class FilterTaxRateByRegionMapper implements Mapper<
  TaxRate_skip_id_,
  TaxRate_skip_value_,
  TaxRate_skip_id_,
  TaxRate_skip_value_
> {
  constructor(private region: string | null) {}

  mapEntry(
    key: TaxRate_skip_id_,
    values: Values<TaxRate_skip_value_>,
    context: Context,
  ): Iterable<[TaxRate_skip_id_, TaxRate_skip_value_]> {
    // > body
    const emits: [TaxRate_skip_id_, TaxRate_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (this.region === null || value.region === this.region) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
