export type ProductId = string;

export type ProductValue = {
  name: string;
  description: string;
  price: number;
  category: string;
  sku: string;
};

export type Product = { id: ProductId } & ProductValue;

export type InventoryId = string;

export type InventoryValue = {
  productId: string;
  quantity: number;
  reservedQuantity: number;
  lastUpdated: number;
};

export type Inventory = { id: InventoryId } & InventoryValue;

export type ProductWithInventoryId = string;

export type ProductWithInventoryValue = {
  name: string;
  description: string;
  price: number;
  category: string;
  sku: string;
  quantity: number;
  reservedQuantity: number;
  availableQuantity: number;
};

export type ProductWithInventory = { id: ProductWithInventoryId } & ProductWithInventoryValue;

export type ProductsCategoryResourceParams = {
  categoryName: string;
};
