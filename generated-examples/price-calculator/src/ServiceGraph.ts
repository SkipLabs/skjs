import type {
  Promotion_skip_id_,
  Promotion,
  Promotion_skip_value_,
  TaxRule_skip_id_,
  TaxRule,
  TaxRule_skip_value_,
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
  readonly promotions: EagerCollection<
    Promotion_skip_id_,
    Promotion_skip_value_
  >;
  readonly taxRules: EagerCollection<TaxRule_skip_id_, TaxRule_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly promotions: EagerCollection<
    Promotion_skip_id_,
    Promotion_skip_value_
  >;
  readonly taxRules: EagerCollection<TaxRule_skip_id_, TaxRule_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_promotions = inputs.promotions;
  const output_taxRules = inputs.taxRules;
  const output_users = inputs.users;
  return {
    promotions: output_promotions,
    taxRules: output_taxRules,
    users: output_users,
  };
}
