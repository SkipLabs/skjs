import { InteractionByUserMapper } from "./mappers/InteractionByUserMapper.js";
import { PurchaseInteractionMapper } from "./mappers/PurchaseInteractionMapper.js";
import { SumReducer } from "./reducers/SumReducer.js";
import type {
  Interaction_skip_id_,
  Interaction,
  Interaction_skip_value_,
  Product_skip_id_,
  Product,
  ProductStored,
  User_skip_id_,
  User,
  User_skip_value_,
  ProductPopularityCount,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly interactions: EagerCollection<
    Interaction_skip_id_,
    Interaction_skip_value_
  >;
  readonly products: EagerCollection<Product_skip_id_, ProductStored>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly interactions: EagerCollection<
    Interaction_skip_id_,
    Interaction_skip_value_
  >;
  readonly interactionsByUser: EagerCollection<User_skip_id_, Interaction>;
  readonly popularityByProduct: EagerCollection<
    Product_skip_id_,
    ProductPopularityCount
  >;
  readonly products: EagerCollection<Product_skip_id_, ProductStored>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const interactionsByUser = inputs.interactions.map(InteractionByUserMapper);
  const output_interactions = inputs.interactions;
  const output_interactionsByUser = interactionsByUser;
  const purchaseCountByProductFeeder = inputs.interactions.map(
    PurchaseInteractionMapper,
  );
  const popularityByProduct = purchaseCountByProductFeeder.reduce(SumReducer);
  const output_popularityByProduct = popularityByProduct;
  const output_products = inputs.products;
  const output_users = inputs.users;
  return {
    interactions: output_interactions,
    interactionsByUser: output_interactionsByUser,
    popularityByProduct: output_popularityByProduct,
    products: output_products,
    users: output_users,
  };
}
