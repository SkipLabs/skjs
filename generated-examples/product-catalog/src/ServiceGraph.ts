import { InventoryAdjustmentByProductMapper } from "./mappers/InventoryAdjustmentByProductMapper.js";
import type {
  Category_skip_id_,
  Category,
  Category_skip_value_,
  InventoryAdjustment_skip_id_,
  InventoryAdjustment,
  InventoryAdjustment_skip_value_,
  Product_skip_id_,
  Product,
  ProductStored,
  User_skip_id_,
  User,
  User_skip_value_,
  ProductIdKey,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly categories: EagerCollection<Category_skip_id_, Category_skip_value_>;
  readonly inventoryAdjustments: EagerCollection<
    InventoryAdjustment_skip_id_,
    InventoryAdjustment_skip_value_
  >;
  readonly products: EagerCollection<Product_skip_id_, ProductStored>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly adjustmentsByProduct: EagerCollection<
    ProductIdKey,
    InventoryAdjustment
  >;
  readonly categories: EagerCollection<Category_skip_id_, Category_skip_value_>;
  readonly products: EagerCollection<Product_skip_id_, ProductStored>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const adjustmentsByProduct = inputs.inventoryAdjustments.map(
    InventoryAdjustmentByProductMapper,
  );
  const output_adjustmentsByProduct = adjustmentsByProduct;
  const output_categories = inputs.categories;
  const output_products = inputs.products;
  const output_users = inputs.users;
  return {
    adjustmentsByProduct: output_adjustmentsByProduct,
    categories: output_categories,
    products: output_products,
    users: output_users,
  };
}
