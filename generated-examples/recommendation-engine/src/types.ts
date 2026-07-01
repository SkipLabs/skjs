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

export type CreateInteractionRequest = {
  readonly productId: string;
  readonly rating?: number;
  readonly type: InteractionType;
} & { readonly [key: string]: Json | null };

export type CreateInteractionRequest_skip_id_ = {
  readonly productId: string;
  readonly rating?: number;
  readonly type: InteractionType;
} & { readonly [key: string]: Json | null };

export type CreateInteractionRequest_skip_value_ = {
  readonly productId: string;
  readonly rating?: number;
  readonly type: InteractionType;
} & { readonly [key: string]: Json | null };

export type CreateProductRequest = {
  readonly category: string;
  readonly description?: string;
  readonly name: string;
  readonly price: number;
  readonly tags?: string[];
} & { readonly [key: string]: Json | null };

export type CreateProductRequest_skip_id_ = {
  readonly category: string;
  readonly description?: string;
  readonly name: string;
  readonly price: number;
  readonly tags?: string[];
} & { readonly [key: string]: Json | null };

export type CreateProductRequest_skip_value_ = {
  readonly category: string;
  readonly description?: string;
  readonly name: string;
  readonly price: number;
  readonly tags?: string[];
} & { readonly [key: string]: Json | null };

export type GetMyInteractionParams = {
  readonly interactionId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type GetProductParams = { readonly productId: string } & {
  readonly [key: string]: Json | null;
};

export type Interaction = {
  readonly id: string;
  readonly occurredAt: string;
  readonly productId: string;
  readonly rating?: number;
  readonly type: InteractionType;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type InteractionList = {
  readonly items: Interaction[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type InteractionList_skip_id_ = {
  readonly items: Interaction[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type InteractionList_skip_value_ = {
  readonly items: Interaction[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type InteractionType = "VIEW" | "ADD_TO_CART" | "PURCHASE" | "RATE";

export type InteractionType_skip_id_ =
  | "VIEW"
  | "ADD_TO_CART"
  | "PURCHASE"
  | "RATE";

export type InteractionType_skip_value_ =
  | "VIEW"
  | "ADD_TO_CART"
  | "PURCHASE"
  | "RATE";

export type Interaction_skip_id_ = string;

export type Interaction_skip_value_ = {
  readonly occurredAt: string;
  readonly productId: string;
  readonly rating?: number;
  readonly type: InteractionType;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type ListMyInteractionsParams = {
  readonly productId?: string;
  readonly type?: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type ListProductsParams = {
  readonly category?: string;
  readonly search?: string;
} & { readonly [key: string]: Json | null };

export type Product = {
  readonly category: string;
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly popularity?: number;
  readonly price: number;
  readonly tags?: string[];
} & { readonly [key: string]: Json | null };

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

export type ProductPopularityCount = number;

export type ProductStored = {
  readonly category: string;
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly price: number;
  readonly tags?: string[];
} & { readonly [key: string]: Json | null };

export type Product_skip_id_ = string;

export type Product_skip_value_ = {
  readonly category: string;
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly popularity?: number;
  readonly price: number;
  readonly tags?: string[];
} & { readonly [key: string]: Json | null };

export type Recommendation = {
  readonly product: Product;
  readonly productId: string;
  readonly reason: string;
  readonly score: number;
} & { readonly [key: string]: Json | null };

export type RecommendationList = { readonly items: Recommendation[] } & {
  readonly [key: string]: Json | null;
};

export type RecommendationList_skip_id_ = {
  readonly items: Recommendation[];
} & { readonly [key: string]: Json | null };

export type RecommendationList_skip_value_ = {
  readonly items: Recommendation[];
} & { readonly [key: string]: Json | null };

export type Recommendation_skip_id_ = {
  readonly product: Product;
  readonly productId: string;
  readonly reason: string;
  readonly score: number;
} & { readonly [key: string]: Json | null };

export type Recommendation_skip_value_ = {
  readonly product: Product;
  readonly productId: string;
  readonly reason: string;
  readonly score: number;
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
  readonly category?: string;
  readonly description?: string;
  readonly name?: string;
  readonly price?: number;
  readonly tags?: string[];
} & { readonly [key: string]: Json | null };

export type UpdateProductRequest_skip_id_ = {
  readonly category?: string;
  readonly description?: string;
  readonly name?: string;
  readonly price?: number;
  readonly tags?: string[];
} & { readonly [key: string]: Json | null };

export type UpdateProductRequest_skip_value_ = {
  readonly category?: string;
  readonly description?: string;
  readonly name?: string;
  readonly price?: number;
  readonly tags?: string[];
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
