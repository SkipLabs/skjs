import type { Book_skip_id_, Book_skip_value_, Book } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetBookStoredResourceInputs extends SharedCollections {
  readonly books: EagerCollection<Book_skip_id_, Book_skip_value_>;
}

export class GetBookStoredResource implements Resource<GetBookStoredResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetBookStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Book_skip_id_, Book_skip_value_> {
    return inputs.books;
  }
}
