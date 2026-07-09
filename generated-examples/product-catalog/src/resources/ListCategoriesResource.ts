import type {
  Category_skip_id_,
  Category_skip_value_,
  Category,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListCategoriesResourceInputs extends SharedCollections {
  readonly categories: EagerCollection<Category_skip_id_, Category_skip_value_>;
}

export class ListCategoriesResource implements Resource<ListCategoriesResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListCategoriesResourceInputs,
    _context: Context,
  ): EagerCollection<Category_skip_id_, Category_skip_value_> {
    return inputs.categories;
  }
}
