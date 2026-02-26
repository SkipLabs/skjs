import type {
  EagerCollection,

  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Reducer,
  Values,
  Nullable,
  DepSafe
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  UserId,
  UserValue,
  ProductId,
  ProductValue,
  InteractionId,
  InteractionValue,
  RecommendationId,
  RecommendationValue,
  ProductsCategoryResourceParams,
  RecommendationsResourceParams,
} from "./types.js";

export type InteractionForPopularity = {
  type: "view" | "purchase" | "wishlist";
};

export type PopularityAccum = {
  viewCount: number;
  wishlistCount: number;
  purchaseCount: number;
  totalScore: number;
};

export type Inputs = {
  users: InputDefinition<UserId, UserValue>;
  products: InputDefinition<ProductId, ProductValue>;
  interactions: InputDefinition<InteractionId, InteractionValue>;
};

export type InputCollections = {
  users: EagerCollection<UserId, UserValue>;
  products: EagerCollection<ProductId, ProductValue>;
  interactions: EagerCollection<InteractionId, InteractionValue>;
};

export type GraphCollections = {
  users: EagerCollection<UserId, UserValue>;
  products: EagerCollection<ProductId, ProductValue>;
  interactions: EagerCollection<InteractionId, InteractionValue>;
  interactionsByUser: EagerCollection<UserId, InteractionValue>;
  productPopularity: EagerCollection<ProductId, PopularityAccum>;
};

export type Resources = {
  "users": ResourceClass<GraphCollections, {}>;
  "products": ResourceClass<GraphCollections, {}>;
  "products-category": ResourceClass<GraphCollections, ProductsCategoryResourceParams>;
  "products-popular": ResourceClass<GraphCollections, {}>;
  "recommendations": ResourceClass<GraphCollections, RecommendationsResourceParams>;
};

export class InteractionsByUserMapper implements Mapper<InteractionId, InteractionValue, UserId, InteractionValue> {
  constructor() {
  }

  mapEntry(
    _key: InteractionId,
    values: Values<InteractionValue>,
    _context: Context
  ): Iterable<[UserId, InteractionValue]> {
    const result: Array<[UserId, InteractionValue]> = Array.of();
    for (const v of values) {
      result.push([v.userId, v]);
    }
    return result;
  }
}

export class InteractionToProductMapper implements Mapper<InteractionId, InteractionValue, ProductId, InteractionForPopularity> {
  constructor() {
  }

  mapEntry(
    _key: InteractionId,
    values: Values<InteractionValue>,
    _context: Context
  ): Iterable<[ProductId, InteractionForPopularity]> {
    const result: Array<[ProductId, InteractionForPopularity]> = Array.of();
    for (const v of values) {
      result.push([v.productId, { type: v.type }]);
    }
    return result;
  }
}

export class ProductsByCategoryMapper implements Mapper<ProductId, ProductValue, ProductId, ProductValue> {
  private category: string;

  constructor(category: string) {
    this.category = category;
  }

  mapEntry(
    key: ProductId,
    values: Values<ProductValue>,
    _context: Context
  ): Iterable<[ProductId, ProductValue]> {
    const result: Array<[ProductId, ProductValue]> = Array.of();
    for (const v of values) {
      if (v.category === this.category) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class RecommendationMapper implements Mapper<ProductId, ProductValue, RecommendationId, RecommendationValue> {
  private userId: string;
  private userPreferences: Array<string>;
  private userInteractions: Array<InteractionValue>;
  private popularityMap: Map<ProductId, PopularityAccum>;
  private interactedProductIds: Set<string>;

  constructor(userId: string, userPreferences: Array<string>, userInteractions: Array<InteractionValue>, popularityMap: Map<ProductId, PopularityAccum>) {
    this.userId = userId;
    this.userPreferences = userPreferences;
    this.userInteractions = userInteractions;
    this.popularityMap = popularityMap;
    this.interactedProductIds = new Set<string>();
    for (const interaction of userInteractions) {
      if (interaction.type === "purchase") {
        this.interactedProductIds.add(interaction.productId);
      }
    }
  }

  mapEntry(
    key: ProductId,
    values: Values<ProductValue>,
    _context: Context
  ): Iterable<[RecommendationId, RecommendationValue]> {
    const result: Array<[RecommendationId, RecommendationValue]> = Array.of();
    for (const product of values) {
      
      if (this.interactedProductIds.has(key)) {
        continue;
      }
      
      let score = 0;
      const reasons: Array<string> = Array.of();
      
      let categoryMatch = false;
      for (let j = 0; j < this.userPreferences.length; j++) {
        if (product.category === this.userPreferences[j]) {
          categoryMatch = true;
          break;
        }
      }
      if (categoryMatch) {
        score = score + 30;
        reasons.push("category match");
      }
      
      let tagMatchCount = 0;
      for (const tag of product.tags) {
        for (let k = 0; k < this.userPreferences.length; k++) {
          if (tag === this.userPreferences[k]) {
            tagMatchCount = tagMatchCount + 1;
            break;
          }
        }
      }
      if (tagMatchCount > 0) {
        score = score + tagMatchCount * 10;
        reasons.push("tag match");
      }
      
      const popularity = this.popularityMap.get(key);
      if (popularity !== undefined) {
        score = score + Math.min(popularity.totalScore, 50);
        if (popularity.totalScore > 10) {
          reasons.push("popular");
        }
      }
      
      score = score + Math.min(product.popularity, 20);
      
      if (score > 0) {
        const recommendationId: RecommendationId = JSON.stringify([this.userId, key]);
        const reason = reasons.length > 0 ? reasons.join(", ") : "general recommendation";
        result.push([recommendationId, {
          userId: this.userId,
          productId: key,
          score: score,
          reason: reason
        }]);
      }
    }
    return result;
  }
}

export class PopularityReducer implements Reducer<InteractionForPopularity, PopularityAccum> {
  initial: Nullable<PopularityAccum> = null;

  constructor() {
  }

  add(accum: Nullable<PopularityAccum>, value: InteractionForPopularity): PopularityAccum {
    const viewWeight = 1;
    const wishlistWeight = 2;
    const purchaseWeight = 3;
    
    let viewCount = 0;
    let wishlistCount = 0;
    let purchaseCount = 0;
    let totalScore = 0;
    
    if (accum !== null) {
      viewCount = accum.viewCount;
      wishlistCount = accum.wishlistCount;
      purchaseCount = accum.purchaseCount;
      totalScore = accum.totalScore;
    }
    
    if (value.type === "view") {
      viewCount = viewCount + 1;
      totalScore = totalScore + viewWeight;
    } else if (value.type === "wishlist") {
      wishlistCount = wishlistCount + 1;
      totalScore = totalScore + wishlistWeight;
    } else if (value.type === "purchase") {
      purchaseCount = purchaseCount + 1;
      totalScore = totalScore + purchaseWeight;
    }
    
    return {
      viewCount: viewCount,
      wishlistCount: wishlistCount,
      purchaseCount: purchaseCount,
      totalScore: totalScore
    };
  }

  remove(accum: PopularityAccum, value: InteractionForPopularity): Nullable<PopularityAccum> {
    const viewWeight = 1;
    const wishlistWeight = 2;
    const purchaseWeight = 3;
    
    let viewCount = accum.viewCount;
    let wishlistCount = accum.wishlistCount;
    let purchaseCount = accum.purchaseCount;
    let totalScore = accum.totalScore;
    
    if (value.type === "view") {
      viewCount = viewCount - 1;
      totalScore = totalScore - viewWeight;
    } else if (value.type === "wishlist") {
      wishlistCount = wishlistCount - 1;
      totalScore = totalScore - wishlistWeight;
    } else if (value.type === "purchase") {
      purchaseCount = purchaseCount - 1;
      totalScore = totalScore - purchaseWeight;
    }
    
    if (viewCount === 0 && wishlistCount === 0 && purchaseCount === 0) {
      return null;
    }
    
    return {
      viewCount: viewCount,
      wishlistCount: wishlistCount,
      purchaseCount: purchaseCount,
      totalScore: totalScore
    };
  }
}

export class UsersResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<UserId, UserValue> {
    return cs.users;
  }
}

export class ProductsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ProductId, ProductValue> {
    return cs.products;
  }
}

export class ProductsCategoryResource implements Resource<GraphCollections> {
  private category: string;

  constructor(params: ProductsCategoryResourceParams) {
    this.category = params.category;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ProductId, ProductValue> {
    return cs.products.map(ProductsByCategoryMapper, this.category);
  }
}

export class ProductsPopularResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ProductId, ProductValue> {
    return cs.products;
  }
}

export class RecommendationsResource implements Resource<GraphCollections> {
  private userId: string;

  constructor(params: RecommendationsResourceParams) {
    this.userId = params.userId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<RecommendationId, RecommendationValue> {
    const userValues = cs.users.getArray(this.userId);
    let userPreferences: Array<string> = Array.of();
    const userEntry = userValues[0];
    if (userEntry !== undefined) {
      userPreferences = userEntry.preferences;
    }
    
    const userInteractions = cs.interactionsByUser.getArray(this.userId);
    
    const popularityMap = new Map<ProductId, PopularityAccum & DepSafe>();
    const productIds = cs.products;
    const allProducts = productIds.slice("", "\uffff");
    const productArr = allProducts.take(10000);
    
    const popularityCollection = cs.productPopularity;
    const popSlice = popularityCollection.slice("", "\uffff");
    const popArr = popSlice.take(10000);
    
    for (let i = 0; i < popArr.size(); i++) {
    }
    
    return cs.products.map(
      RecommendationMapper,
      this.userId,
      userPreferences,
      userInteractions,
      popularityMap
    );
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  public inputs: Inputs;
  public resources: Resources;

  constructor() {
                this.inputs = { users: new InputDefinition<UserId, UserValue>([]), products: new InputDefinition<ProductId, ProductValue>([]), interactions: new InputDefinition<InteractionId, InteractionValue>([]) };
    this.resources = { "users": UsersResource, "products": ProductsResource, "products-category": ProductsCategoryResource, "products-popular": ProductsPopularResource, "recommendations": RecommendationsResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const interactionsByUser = inputs.interactions.map(InteractionsByUserMapper);
    const productPopularity = inputs.interactions.map(InteractionToProductMapper).reduce(PopularityReducer);
    
    return {
      users: inputs.users,
      products: inputs.products,
      interactions: inputs.interactions,
      interactionsByUser: interactionsByUser,
      productPopularity: productPopularity
    };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}
