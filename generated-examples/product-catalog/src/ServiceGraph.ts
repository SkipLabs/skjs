import type {
  Category_skip_id_,
  Category,
  Category_skip_value_,
  InventoryAdjustment_skip_id_,
  InventoryAdjustment,
  InventoryAdjustment_skip_value_,
  InventoryItem_skip_id_,
  InventoryItem,
  InventoryItem_skip_value_,
  Product_skip_id_,
  Product,
  Product_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  Warehouse_skip_id_,
  Warehouse,
  Warehouse_skip_value_,
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
  readonly inventoryItems: EagerCollection<
    InventoryItem_skip_id_,
    InventoryItem_skip_value_
  >;
  readonly products: EagerCollection<Product_skip_id_, Product_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
  readonly warehouses: EagerCollection<
    Warehouse_skip_id_,
    Warehouse_skip_value_
  >;
}

export interface GraphCollections extends SharedCollections {
  readonly categories: EagerCollection<Category_skip_id_, Category_skip_value_>;
  readonly inventoryAdjustments: EagerCollection<
    InventoryAdjustment_skip_id_,
    InventoryAdjustment_skip_value_
  >;
  readonly inventoryItems: EagerCollection<
    InventoryItem_skip_id_,
    InventoryItem_skip_value_
  >;
  readonly products: EagerCollection<Product_skip_id_, Product_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
  readonly warehouses: EagerCollection<
    Warehouse_skip_id_,
    Warehouse_skip_value_
  >;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_categories = inputs.categories;
  const output_inventoryAdjustments = inputs.inventoryAdjustments;
  const output_inventoryItems = inputs.inventoryItems;
  const output_products = inputs.products;
  const output_users = inputs.users;
  const output_warehouses = inputs.warehouses;
  return {
    categories: output_categories,
    inventoryAdjustments: output_inventoryAdjustments,
    inventoryItems: output_inventoryItems,
    products: output_products,
    users: output_users,
    warehouses: output_warehouses,
  };
}
