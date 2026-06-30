export type AdjustmentReason =
  | "RESTOCK"
  | "SALE"
  | "RETURN"
  | "DAMAGE"
  | "TRANSFER_IN"
  | "TRANSFER_OUT"
  | "CORRECTION";

export type AdjustmentReason_skip_id_ =
  | "RESTOCK"
  | "SALE"
  | "RETURN"
  | "DAMAGE"
  | "TRANSFER_IN"
  | "TRANSFER_OUT"
  | "CORRECTION";

export type AdjustmentReason_skip_value_ =
  | "RESTOCK"
  | "SALE"
  | "RETURN"
  | "DAMAGE"
  | "TRANSFER_IN"
  | "TRANSFER_OUT"
  | "CORRECTION";

export type ApiError = {
  readonly code: string;
  readonly details?: string;
  readonly message: string;
};

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly details?: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly details?: string;
  readonly message: string;
};

export type Category = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt: string;
};

export type CategoryList = {
  readonly items: Category[];
  readonly total: number;
};

export type CategoryList_skip_id_ = {
  readonly items: Category[];
  readonly total: number;
};

export type CategoryList_skip_value_ = {
  readonly items: Category[];
  readonly total: number;
};

export type Category_skip_id_ = string;

export type Category_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt: string;
};

export type CreateCategoryRequest = {
  readonly description?: string;
  readonly name: string;
};

export type CreateCategoryRequest_skip_id_ = {
  readonly description?: string;
  readonly name: string;
};

export type CreateCategoryRequest_skip_value_ = {
  readonly description?: string;
  readonly name: string;
};

export type CreateInventoryAdjustmentRequest = {
  readonly delta: number;
  readonly note?: string;
  readonly reason: AdjustmentReason;
};

export type CreateInventoryAdjustmentRequest_skip_id_ = {
  readonly delta: number;
  readonly note?: string;
  readonly reason: AdjustmentReason;
};

export type CreateInventoryAdjustmentRequest_skip_value_ = {
  readonly delta: number;
  readonly note?: string;
  readonly reason: AdjustmentReason;
};

export type CreateProductRequest = {
  readonly categoryId: string;
  readonly currency: string;
  readonly description?: string;
  readonly imageUrl?: string;
  readonly name: string;
  readonly price: number;
  readonly sku: string;
  readonly status?: ProductStatus;
};

export type CreateProductRequest_skip_id_ = {
  readonly categoryId: string;
  readonly currency: string;
  readonly description?: string;
  readonly imageUrl?: string;
  readonly name: string;
  readonly price: number;
  readonly sku: string;
  readonly status?: ProductStatus;
};

export type CreateProductRequest_skip_value_ = {
  readonly categoryId: string;
  readonly currency: string;
  readonly description?: string;
  readonly imageUrl?: string;
  readonly name: string;
  readonly price: number;
  readonly sku: string;
  readonly status?: ProductStatus;
};

export type CreateWarehouseRequest = {
  readonly address?: string;
  readonly name: string;
};

export type CreateWarehouseRequest_skip_id_ = {
  readonly address?: string;
  readonly name: string;
};

export type CreateWarehouseRequest_skip_value_ = {
  readonly address?: string;
  readonly name: string;
};

export type GetInventoryItemParams = {
  readonly productId: string;
  readonly warehouseId: string;
};

export type InventoryAdjustment = {
  readonly actorUserId: string;
  readonly delta: number;
  readonly id: string;
  readonly note?: string;
  readonly occurredAt: string;
  readonly productId: string;
  readonly reason: AdjustmentReason;
  readonly resultingQuantity: number;
  readonly warehouseId: string;
};

export type InventoryAdjustmentList = {
  readonly items: InventoryAdjustment[];
  readonly total: number;
};

export type InventoryAdjustmentList_skip_id_ = {
  readonly items: InventoryAdjustment[];
  readonly total: number;
};

export type InventoryAdjustmentList_skip_value_ = {
  readonly items: InventoryAdjustment[];
  readonly total: number;
};

export type InventoryAdjustment_skip_id_ = string;

export type InventoryAdjustment_skip_value_ = {
  readonly actorUserId: string;
  readonly delta: number;
  readonly note?: string;
  readonly occurredAt: string;
  readonly productId: string;
  readonly reason: AdjustmentReason;
  readonly resultingQuantity: number;
  readonly warehouseId: string;
};

export type InventoryItem = {
  readonly createdAt: string;
  readonly productId: string;
  readonly quantity: number;
  readonly reorderThreshold: number;
  readonly updatedAt: string;
  readonly warehouseId: string;
};

export type InventoryItemKey = {
  readonly productId: string;
  readonly warehouseId: string;
};

export type InventoryItemList = {
  readonly items: InventoryItem[];
  readonly total: number;
};

export type InventoryItemList_skip_id_ = {
  readonly items: InventoryItem[];
  readonly total: number;
};

export type InventoryItemList_skip_value_ = {
  readonly items: InventoryItem[];
  readonly total: number;
};

export type InventoryItem_skip_id_ = {
  readonly productId: string;
  readonly warehouseId: string;
};

export type InventoryItem_skip_value_ = {
  readonly createdAt: string;
  readonly quantity: number;
  readonly reorderThreshold: number;
  readonly updatedAt: string;
};

export type ListAdjustmentsByInventoryParams = {
  readonly productId: string;
  readonly warehouseId: string;
};

export type Product = {
  readonly categoryId: string;
  readonly createdAt: string;
  readonly currency: string;
  readonly description?: string;
  readonly id: string;
  readonly imageUrl?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly price: number;
  readonly sku: string;
  readonly status: ProductStatus;
  readonly updatedAt: string;
};

export type ProductList = { readonly items: Product[]; readonly total: number };

export type ProductList_skip_id_ = {
  readonly items: Product[];
  readonly total: number;
};

export type ProductList_skip_value_ = {
  readonly items: Product[];
  readonly total: number;
};

export type ProductStatus = "DRAFT" | "ACTIVE" | "DISCONTINUED";

export type ProductStatus_skip_id_ = "DRAFT" | "ACTIVE" | "DISCONTINUED";

export type ProductStatus_skip_value_ = "DRAFT" | "ACTIVE" | "DISCONTINUED";

export type Product_skip_id_ = string;

export type Product_skip_value_ = {
  readonly categoryId: string;
  readonly createdAt: string;
  readonly currency: string;
  readonly description?: string;
  readonly imageUrl?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly price: number;
  readonly sku: string;
  readonly status: ProductStatus;
  readonly updatedAt: string;
};

export type UpdateCategoryRequest = {
  readonly description?: string;
  readonly name?: string;
};

export type UpdateCategoryRequest_skip_id_ = {
  readonly description?: string;
  readonly name?: string;
};

export type UpdateCategoryRequest_skip_value_ = {
  readonly description?: string;
  readonly name?: string;
};

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
};

export type UpdateProductRequest = {
  readonly categoryId?: string;
  readonly currency?: string;
  readonly description?: string;
  readonly imageUrl?: string;
  readonly name?: string;
  readonly price?: number;
  readonly sku?: string;
  readonly status?: ProductStatus;
};

export type UpdateProductRequest_skip_id_ = {
  readonly categoryId?: string;
  readonly currency?: string;
  readonly description?: string;
  readonly imageUrl?: string;
  readonly name?: string;
  readonly price?: number;
  readonly sku?: string;
  readonly status?: ProductStatus;
};

export type UpdateProductRequest_skip_value_ = {
  readonly categoryId?: string;
  readonly currency?: string;
  readonly description?: string;
  readonly imageUrl?: string;
  readonly name?: string;
  readonly price?: number;
  readonly sku?: string;
  readonly status?: ProductStatus;
};

export type UpdateWarehouseRequest = {
  readonly address?: string;
  readonly name?: string;
};

export type UpdateWarehouseRequest_skip_id_ = {
  readonly address?: string;
  readonly name?: string;
};

export type UpdateWarehouseRequest_skip_value_ = {
  readonly address?: string;
  readonly name?: string;
};

export type UpsertInventoryItemRequest = {
  readonly quantity: number;
  readonly reorderThreshold?: number;
};

export type UpsertInventoryItemRequest_skip_id_ = {
  readonly quantity: number;
  readonly reorderThreshold?: number;
};

export type UpsertInventoryItemRequest_skip_value_ = {
  readonly quantity: number;
  readonly reorderThreshold?: number;
};

export type User = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
  readonly updatedAt?: string;
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly updatedAt?: string;
};

export type Warehouse = {
  readonly address?: string;
  readonly createdAt: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt: string;
};

export type WarehouseList = {
  readonly items: Warehouse[];
  readonly total: number;
};

export type WarehouseList_skip_id_ = {
  readonly items: Warehouse[];
  readonly total: number;
};

export type WarehouseList_skip_value_ = {
  readonly items: Warehouse[];
  readonly total: number;
};

export type Warehouse_skip_id_ = string;

export type Warehouse_skip_value_ = {
  readonly address?: string;
  readonly createdAt: string;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt: string;
};
