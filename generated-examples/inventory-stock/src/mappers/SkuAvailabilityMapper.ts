import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Sku_skip_id_,
  Sku_skip_value_,
  SkuAvailability,
  Receipt,
  Order,
  Sku,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each sku entry, consult receiptsBySku for the receipts indexed by the entry's key to obtain all receipt values for that sku; sum the quantity field over receipts whose status equals the literal 'RECEIVED' to compute totalReceived (default zero when no such receipts). Consult ordersBySku for the orders indexed by the entry's key to obtain all order values for that sku; sum the quantity field over orders whose status equals the literal 'ALLOCATED' or the literal 'FULFILLED' to compute totalAllocated (default zero); sum the quantity field over orders whose status equals the literal 'ALLOCATED' to compute totalReserved (default zero). Compute totalOnHand as totalReceived minus totalAllocated. Compute available as totalOnHand minus totalReserved. Compute belowReorderThreshold as true when the entry's value's reorderThreshold field is present AND available is strictly less than that reorderThreshold; false otherwise. Emit one output pair whose key is the entry's key and whose value lists every required field of SkuAvailability explicitly: skuId sourced from the entry's key; totalReceived, totalAllocated, totalReserved, totalOnHand, available, belowReorderThreshold sourced from the computed values.
export class SkuAvailabilityMapper implements Mapper<
  Sku_skip_id_,
  Sku_skip_value_,
  Sku_skip_id_,
  SkuAvailability
> {
  constructor(
    private receiptsBySku: EagerCollection<Sku_skip_id_, Receipt>,
    private ordersBySku: EagerCollection<Sku_skip_id_, Order>,
  ) {}

  mapEntry(
    key: Sku_skip_id_,
    values: Values<Sku_skip_value_>,
    context: Context,
  ): Iterable<[Sku_skip_id_, SkuAvailability]> {
    // > body
    const emits: [Sku_skip_id_, SkuAvailability][] = [];
    for (const value of values.toArray()) {
      const receipts = this.receiptsBySku.getArray(key);
      let totalReceived = 0;
      for (const receipt of receipts) {
        if (receipt.status === "RECEIVED") {
          totalReceived += receipt.quantity;
        }
      }

      const orders = this.ordersBySku.getArray(key);
      let totalAllocated = 0;
      let totalReserved = 0;
      for (const order of orders) {
        if (order.status === "ALLOCATED" || order.status === "FULFILLED") {
          totalAllocated += order.quantity;
        }
        if (order.status === "ALLOCATED") {
          totalReserved += order.quantity;
        }
      }

      const totalOnHand = totalReceived - totalAllocated;
      const available = totalOnHand - totalReserved;
      const belowReorderThreshold =
        value.reorderThreshold !== undefined &&
        available < value.reorderThreshold;

      const out: SkuAvailability = {
        skuId: key,
        totalReceived,
        totalAllocated,
        totalReserved,
        totalOnHand,
        available,
        belowReorderThreshold,
      };
      emits.push([key, out]);
    }
    return emits;
    // < body
  }
}
