export type ViewPurchaseWishlistEnum = "view" | "purchase" | "wishlist";

export type UserId = string;

export type UserValue = {
  name: string;
  email: string;
  preferences: Array<string>;
  createdAt: number;
};

export type User = UserValue & { id: UserId };

export type ProductId = string;

export type ProductValue = {
  name: string;
  description: string;
  category: string;
  price: number;
  tags: Array<string>;
  popularity: number;
};

export type Product = ProductValue & { id: ProductId };

export type InteractionId = string;

export type InteractionValue = {
  userId: string;
  productId: string;
  type: ViewPurchaseWishlistEnum;
  timestamp: number;
  rating: number | null;
};

export type Interaction = InteractionValue & { id: InteractionId };

export type RecommendationId = string;

export type RecommendationValue = {
  userId: string;
  productId: string;
  score: number;
  reason: string;
};

export type Recommendation = RecommendationValue & { id: RecommendationId };

export type ProductsCategoryResourceParams = {
  category: string;
};

export type RecommendationsResourceParams = {
  userId: string;
};
