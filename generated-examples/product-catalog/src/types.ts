import type { Json } from "@skipruntime/core";

export type ApiError = { readonly code: string; readonly message: string } & {
  readonly [key: string]: Json | null;
};

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type Category = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type CategoryList = {
  readonly items: Category[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type CategoryList_skip_id_ = {
  readonly items: Category[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type CategoryList_skip_value_ = {
  readonly items: Category[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type Category_skip_id_ = string;

export type Category_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type CreateCategoryRequest = {
  readonly description?: string;
  readonly name: string;
} & { readonly [key: string]: Json | null };

export type CreateCategoryRequest_skip_id_ = {
  readonly description?: string;
  readonly name: string;
} & { readonly [key: string]: Json | null };

export type CreateCategoryRequest_skip_value_ = {
  readonly description?: string;
  readonly name: string;
} & { readonly [key: string]: Json | null };

export type CreateInventoryAdjustmentRequest = {
  readonly delta: number;
  readonly reason?: string;
} & { readonly [key: string]: Json | null };

export type CreateInventoryAdjustmentRequest_skip_id_ = {
  readonly delta: number;
  readonly reason?: string;
} & { readonly [key: string]: Json | null };

export type CreateInventoryAdjustmentRequest_skip_value_ = {
  readonly delta: number;
  readonly reason?: string;
} & { readonly [key: string]: Json | null };

export type CreateProductRequest = {
  readonly categoryId?: string;
  readonly currency: string;
  readonly description?: string;
  readonly name: string;
  readonly price: number;
  readonly sku?: string;
  readonly stockQuantity?: number;
} & { readonly [key: string]: Json | null };

export type CreateProductRequest_skip_id_ = {
  readonly categoryId?: string;
  readonly currency: string;
  readonly description?: string;
  readonly name: string;
  readonly price: number;
  readonly sku?: string;
  readonly stockQuantity?: number;
} & { readonly [key: string]: Json | null };

export type CreateProductRequest_skip_value_ = {
  readonly categoryId?: string;
  readonly currency: string;
  readonly description?: string;
  readonly name: string;
  readonly price: number;
  readonly sku?: string;
  readonly stockQuantity?: number;
} & { readonly [key: string]: Json | null };

export type InventoryAdjustment = {
  readonly actorId: string;
  readonly createdAt: string;
  readonly delta: number;
  readonly id: string;
  readonly productId: string;
  readonly reason?: string;
  readonly resultingStock: number;
} & { readonly [key: string]: Json | null };

export type InventoryAdjustmentList = {
  readonly items: InventoryAdjustment[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type InventoryAdjustmentList_skip_id_ = {
  readonly items: InventoryAdjustment[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type InventoryAdjustmentList_skip_value_ = {
  readonly items: InventoryAdjustment[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type InventoryAdjustment_skip_id_ = string;

export type InventoryAdjustment_skip_value_ = {
  readonly actorId: string;
  readonly createdAt: string;
  readonly delta: number;
  readonly productId: string;
  readonly reason?: string;
  readonly resultingStock: number;
} & { readonly [key: string]: Json | null };

export type ListInventoryAdjustmentsParams = { readonly productId: string } & {
  readonly [key: string]: Json | null;
};

export type ListProductsParams = {
  readonly categoryId?: string;
  readonly inStock?: boolean;
  readonly ownerId?: string;
  readonly search?: string;
} & { readonly [key: string]: Json | null };

export type Product = {
  readonly categoryId?: string;
  readonly createdAt: string;
  readonly currency: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly price: number;
  readonly sku?: string;
  readonly stockQuantity: number;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type ProductIdKey = string;

export type ProductList = {
  readonly items: Product[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type ProductList_skip_id_ = {
  readonly items: Product[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type ProductList_skip_value_ = {
  readonly items: Product[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type ProductStored = {
  readonly categoryId?: string;
  readonly createdAt: string;
  readonly currency: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly price: number;
  readonly sku?: string;
  readonly stockQuantity: number;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type Product_skip_id_ = string;

export type Product_skip_value_ = {
  readonly categoryId?: string;
  readonly createdAt: string;
  readonly currency: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly price: number;
  readonly sku?: string;
  readonly stockQuantity: number;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type UpdateCategoryRequest = {
  readonly description?: string;
  readonly name?: string;
} & { readonly [key: string]: Json | null };

export type UpdateCategoryRequest_skip_id_ = {
  readonly description?: string;
  readonly name?: string;
} & { readonly [key: string]: Json | null };

export type UpdateCategoryRequest_skip_value_ = {
  readonly description?: string;
  readonly name?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateProductRequest = {
  readonly categoryId?: string;
  readonly currency?: string;
  readonly description?: string;
  readonly name?: string;
  readonly price?: number;
  readonly sku?: string;
} & { readonly [key: string]: Json | null };

export type UpdateProductRequest_skip_id_ = {
  readonly categoryId?: string;
  readonly currency?: string;
  readonly description?: string;
  readonly name?: string;
  readonly price?: number;
  readonly sku?: string;
} & { readonly [key: string]: Json | null };

export type UpdateProductRequest_skip_value_ = {
  readonly categoryId?: string;
  readonly currency?: string;
  readonly description?: string;
  readonly name?: string;
  readonly price?: number;
  readonly sku?: string;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };
