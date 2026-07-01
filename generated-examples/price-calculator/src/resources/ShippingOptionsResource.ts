import type {
  ShippingOption_skip_id_,
  ShippingOption_skip_value_,
  ShippingOption,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ShippingOptionsResourceInputs extends SharedCollections {
  readonly shippingOptions: EagerCollection<
    ShippingOption_skip_id_,
    ShippingOption_skip_value_
  >;
}

export class ShippingOptionsResource implements Resource<ShippingOptionsResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ShippingOptionsResourceInputs,
    _context: Context,
  ): EagerCollection<ShippingOption_skip_id_, ShippingOption_skip_value_> {
    return inputs.shippingOptions;
  }
}
