import type {
  Warehouse_skip_id_,
  Warehouse_skip_value_,
  Warehouse,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListWarehousesResourceInputs extends SharedCollections {
  readonly warehouses: EagerCollection<
    Warehouse_skip_id_,
    Warehouse_skip_value_
  >;
}

export class ListWarehousesResource implements Resource<ListWarehousesResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListWarehousesResourceInputs,
    _context: Context,
  ): EagerCollection<Warehouse_skip_id_, Warehouse_skip_value_> {
    return inputs.warehouses;
  }
}
