import type {
  Category_skip_id_,
  Category,
  Category_skip_value_,
  Interaction_skip_id_,
  Interaction,
  Interaction_skip_value_,
  Product_skip_id_,
  Product,
  Product_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly categories: EagerCollection<Category_skip_id_, Category_skip_value_>;
  readonly interactions: EagerCollection<
    Interaction_skip_id_,
    Interaction_skip_value_
  >;
  readonly products: EagerCollection<Product_skip_id_, Product_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly categories: EagerCollection<Category_skip_id_, Category_skip_value_>;
  readonly interactions: EagerCollection<
    Interaction_skip_id_,
    Interaction_skip_value_
  >;
  readonly products: EagerCollection<Product_skip_id_, Product_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_categories = inputs.categories;
  const output_interactions = inputs.interactions;
  const output_products = inputs.products;
  const output_users = inputs.users;
  return {
    categories: output_categories,
    interactions: output_interactions,
    products: output_products,
    users: output_users,
  };
}
