export type ApiError = { readonly code: string; readonly message: string };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
};

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
};

export type Category = {
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
};

export type Category_skip_id_ = string;

export type Category_skip_value_ = {
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
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

export type CreateInteractionRequest = {
  readonly productId: string;
  readonly rating?: number;
  readonly type: InteractionType;
};

export type CreateInteractionRequest_skip_id_ = {
  readonly productId: string;
  readonly rating?: number;
  readonly type: InteractionType;
};

export type CreateInteractionRequest_skip_value_ = {
  readonly productId: string;
  readonly rating?: number;
  readonly type: InteractionType;
};

export type CreateProductRequest = {
  readonly categoryId: string;
  readonly description?: string;
  readonly imageUrl?: string;
  readonly name: string;
  readonly priceCents: number;
  readonly tags?: string[];
};

export type CreateProductRequest_skip_id_ = {
  readonly categoryId: string;
  readonly description?: string;
  readonly imageUrl?: string;
  readonly name: string;
  readonly priceCents: number;
  readonly tags?: string[];
};

export type CreateProductRequest_skip_value_ = {
  readonly categoryId: string;
  readonly description?: string;
  readonly imageUrl?: string;
  readonly name: string;
  readonly priceCents: number;
  readonly tags?: string[];
};

export type GetMyRecommendationsParams = {
  readonly categoryId?: string;
  readonly userId: string;
};

export type GetProductParams = { readonly productId: string };

export type Interaction = {
  readonly id: string;
  readonly occurredAt: string;
  readonly productId: string;
  readonly rating?: number;
  readonly type: InteractionType;
  readonly userId: string;
};

export type InteractionList = {
  readonly items: Interaction[];
  readonly total: number;
};

export type InteractionList_skip_id_ = {
  readonly items: Interaction[];
  readonly total: number;
};

export type InteractionList_skip_value_ = {
  readonly items: Interaction[];
  readonly total: number;
};

export type InteractionType = "VIEW" | "CLICK" | "PURCHASE" | "RATE";

export type InteractionType_skip_id_ = "VIEW" | "CLICK" | "PURCHASE" | "RATE";

export type InteractionType_skip_value_ =
  | "VIEW"
  | "CLICK"
  | "PURCHASE"
  | "RATE";

export type Interaction_skip_id_ = string;

export type Interaction_skip_value_ = {
  readonly occurredAt: string;
  readonly productId: string;
  readonly rating?: number;
  readonly type: InteractionType;
  readonly userId: string;
};

export type ListMyInteractionsParams = {
  readonly productId?: string;
  readonly type?: string;
  readonly userId: string;
};

export type ListProductsParams = {
  readonly categoryId?: string;
  readonly q?: string;
};

export type Product = {
  readonly categoryId: string;
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly imageUrl?: string;
  readonly name: string;
  readonly priceCents: number;
  readonly tags?: string[];
  readonly updatedAt?: string;
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

export type Product_skip_id_ = string;

export type Product_skip_value_ = {
  readonly categoryId: string;
  readonly createdAt: string;
  readonly description?: string;
  readonly imageUrl?: string;
  readonly name: string;
  readonly priceCents: number;
  readonly tags?: string[];
  readonly updatedAt?: string;
};

export type Recommendation = {
  readonly productId: string;
  readonly reasonCategoryId?: string;
  readonly score: number;
};

export type RecommendationList = { readonly items: Recommendation[] };

export type RecommendationList_skip_id_ = { readonly items: Recommendation[] };

export type RecommendationList_skip_value_ = {
  readonly items: Recommendation[];
};

export type Recommendation_skip_id_ = {
  readonly productId: string;
  readonly reasonCategoryId?: string;
  readonly score: number;
};

export type Recommendation_skip_value_ = {
  readonly productId: string;
  readonly reasonCategoryId?: string;
  readonly score: number;
};

export type UpdateMeRequest = {
  readonly displayName?: string;
  readonly email?: string;
  readonly preferredCategoryIds?: string[];
};

export type UpdateMeRequest_skip_id_ = {
  readonly displayName?: string;
  readonly email?: string;
  readonly preferredCategoryIds?: string[];
};

export type UpdateMeRequest_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
  readonly preferredCategoryIds?: string[];
};

export type UpdateProductRequest = {
  readonly categoryId?: string;
  readonly description?: string;
  readonly imageUrl?: string;
  readonly name?: string;
  readonly priceCents?: number;
  readonly tags?: string[];
};

export type UpdateProductRequest_skip_id_ = {
  readonly categoryId?: string;
  readonly description?: string;
  readonly imageUrl?: string;
  readonly name?: string;
  readonly priceCents?: number;
  readonly tags?: string[];
};

export type UpdateProductRequest_skip_value_ = {
  readonly categoryId?: string;
  readonly description?: string;
  readonly imageUrl?: string;
  readonly name?: string;
  readonly priceCents?: number;
  readonly tags?: string[];
};

export type User = {
  readonly createdAt: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
  readonly preferredCategoryIds: string[];
};

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly createdAt: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly preferredCategoryIds: string[];
};
